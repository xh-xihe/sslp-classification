import SixQubit.CodeOrbit6
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
namespace MainTheory.Orbit6PhysicalRowData
open scoped BigOperators Matrix
open SixQubit SixQubit.Orbit6
noncomputable section

def RowData (c d : SS.State 6 ℂ) : Prop :=
  (star (c y0) * d z5 + star (c y11) * d z15 = 0) ∧
  (star (c y0) * d z3 + star (c y11) * d z13 = 0) ∧
  (star (c y0) * d z2 + star (c y11) * d z12 = 0) ∧
  (star (c y0) * d z1 + star (c y11) * d z11 = 0) ∧
  (star (c y0) * d z0 + star (c y11) * d z10 = 0) ∧
  (star (c y11) * c y0 + star (c y12) * c y1 + star (c y13) * c y2 + star (c y14) * c y3 + star (c y15) * c y4 + star (c y16) * c y5 + star (c y17) * c y6 + star (c y18) * c y7 + star (c y19) * c y8 + star (c y20) * c y9 + star (c y21) * c y10
      = star (d z15) * d z5 + star (d z13) * d z3 + star (d z12) * d z2 + star (d z11) * d z1 + star (d z10) * d z0 + star (d z14) * d z4 + star (d z16) * d z6 + star (d z17) * d z7 + star (d z18) * d z8 + star (d z19) * d z9) ∧
  (star (c y0) * c y11 + star (c y1) * c y12 + star (c y2) * c y13 + star (c y3) * c y14 + star (c y4) * c y15 + star (c y5) * c y16 + star (c y6) * c y17 + star (c y7) * c y18 + star (c y8) * c y19 + star (c y9) * c y20 + star (c y10) * c y21
      = star (d z5) * d z15 + star (d z3) * d z13 + star (d z2) * d z12 + star (d z1) * d z11 + star (d z0) * d z10 + star (d z4) * d z14 + star (d z6) * d z16 + star (d z7) * d z17 + star (d z8) * d z18 + star (d z9) * d z19) ∧
  (star (c y0) * c y0 + star (c y1) * c y1 + star (c y2) * c y2 + star (c y3) * c y3 + star (c y4) * c y4 + star (c y5) * c y5 + star (c y6) * c y6 + star (c y7) * c y7 + star (c y8) * c y8 + star (c y9) * c y9 + star (c y10) * c y10
      = star (d z5) * d z5 + star (d z3) * d z3 + star (d z2) * d z2 + star (d z1) * d z1 + star (d z0) * d z0 + star (d z4) * d z4 + star (d z6) * d z6 + star (d z7) * d z7 + star (d z8) * d z8 + star (d z9) * d z9) ∧
  (star (c y11) * c y11 + star (c y12) * c y12 + star (c y13) * c y13 + star (c y14) * c y14 + star (c y15) * c y15 + star (c y16) * c y16 + star (c y17) * c y17 + star (c y18) * c y18 + star (c y19) * c y19 + star (c y20) * c y20 + star (c y21) * c y21
      = star (d z15) * d z15 + star (d z13) * d z13 + star (d z12) * d z12 + star (d z11) * d z11 + star (d z10) * d z10 + star (d z14) * d z14 + star (d z16) * d z16 + star (d z17) * d z17 + star (d z18) * d z18 + star (d z19) * d z19) ∧
  (star (c y1) * c y0 + star (c y12) * c y11 = 0) ∧
  (star (c y2) * c y0 + star (c y13) * c y11 = 0) ∧
  (star (c y3) * c y0 + star (c y14) * c y11 = 0) ∧
  (star (c y4) * c y0 + star (c y15) * c y11 = 0) ∧
  (star (c y5) * c y0 + star (c y16) * c y11 = 0) ∧
  (star (c y6) * c y0 + star (c y17) * c y11 = 0) ∧
  (star (c y7) * c y0 + star (c y18) * c y11 = 0) ∧
  (star (c y8) * c y0 + star (c y19) * c y11 = 0) ∧
  (star (c y9) * c y0 + star (c y20) * c y11 = 0) ∧
  (star (c y10) * c y0 + star (c y21) * c y11 = 0) ∧
  (star (c y0) * d z5
      + star (c y1) * d z6
      + star (c y2) * d z7
      + star (c y3) * d z8
      + star (c y4) * d z9
      = 0) ∧
  (star (c y0) * d z15
      + star (c y1) * d z16
      + star (c y2) * d z17
      + star (c y3) * d z18
      + star (c y4) * d z19
      = 0) ∧
  (star (c y11) * d z5
      + star (c y12) * d z6
      + star (c y13) * d z7
      + star (c y14) * d z8
      + star (c y15) * d z9
      = 0) ∧
  (star (c y11) * d z15
      + star (c y12) * d z16
      + star (c y13) * d z17
      + star (c y14) * d z18
      + star (c y15) * d z19
      = 0) ∧
  (star (c y0) * d z3
      + star (c y1) * d z4
      + star (c y5) * d z7
      + star (c y6) * d z8
      + star (c y7) * d z9
      = 0) ∧
  (star (c y0) * d z13
      + star (c y1) * d z14
      + star (c y5) * d z17
      + star (c y6) * d z18
      + star (c y7) * d z19
      = 0) ∧
  (star (c y11) * d z3
      + star (c y12) * d z4
      + star (c y16) * d z7
      + star (c y17) * d z8
      + star (c y18) * d z9
      = 0) ∧
  (star (c y11) * d z13
      + star (c y12) * d z14
      + star (c y16) * d z17
      + star (c y17) * d z18
      + star (c y18) * d z19
      = 0) ∧
  (star (c y0) * d z2
      + star (c y2) * d z4
      + star (c y5) * d z6
      + star (c y8) * d z8
      + star (c y9) * d z9
      = 0) ∧
  (star (c y0) * d z12
      + star (c y2) * d z14
      + star (c y5) * d z16
      + star (c y8) * d z18
      + star (c y9) * d z19
      = 0) ∧
  (star (c y11) * d z2
      + star (c y13) * d z4
      + star (c y16) * d z6
      + star (c y19) * d z8
      + star (c y20) * d z9
      = 0) ∧
  (star (c y11) * d z12
      + star (c y13) * d z14
      + star (c y16) * d z16
      + star (c y19) * d z18
      + star (c y20) * d z19
      = 0) ∧
  (star (c y0) * d z1
      + star (c y3) * d z4
      + star (c y6) * d z6
      + star (c y8) * d z7
      + star (c y10) * d z9
      = 0) ∧
  (star (c y0) * d z11
      + star (c y3) * d z14
      + star (c y6) * d z16
      + star (c y8) * d z17
      + star (c y10) * d z19
      = 0) ∧
  (star (c y11) * d z1
      + star (c y14) * d z4
      + star (c y17) * d z6
      + star (c y19) * d z7
      + star (c y21) * d z9
      = 0) ∧
  (star (c y11) * d z11
      + star (c y14) * d z14
      + star (c y17) * d z16
      + star (c y19) * d z17
      + star (c y21) * d z19
      = 0) ∧
  (star (c y0) * d z0
      + star (c y4) * d z4
      + star (c y7) * d z6
      + star (c y9) * d z7
      + star (c y10) * d z8
      = 0) ∧
  (star (c y0) * d z10
      + star (c y4) * d z14
      + star (c y7) * d z16
      + star (c y9) * d z17
      + star (c y10) * d z18
      = 0) ∧
  (star (c y11) * d z0
      + star (c y15) * d z4
      + star (c y18) * d z6
      + star (c y20) * d z7
      + star (c y21) * d z8
      = 0) ∧
  (star (c y11) * d z10
      + star (c y15) * d z14
      + star (c y18) * d z16
      + star (c y20) * d z17
      + star (c y21) * d z18
      = 0) ∧
  (Complex.normSq (c y0) + Complex.normSq (c y11) = 1/3) ∧
  (Complex.normSq (d z4) + Complex.normSq (d z14) + Complex.normSq (d z6) + Complex.normSq (d z16) + Complex.normSq (d z7) + Complex.normSq (d z17) + Complex.normSq (d z8) + Complex.normSq (d z18) + Complex.normSq (d z9) + Complex.normSq (d z19) = 1/3) ∧
  (Complex.normSq (d z5) + Complex.normSq (d z15) + Complex.normSq (d z3) + Complex.normSq (d z13) + Complex.normSq (d z2) + Complex.normSq (d z12) + Complex.normSq (d z1) + Complex.normSq (d z11) + Complex.normSq (d z0) + Complex.normSq (d z10) = 2/3) ∧
  (c y0 * d z14 - c y11 * d z4 = 0) ∧
  (c y0 * d z16 - c y11 * d z6 = 0) ∧
  (c y0 * d z17 - c y11 * d z7 = 0) ∧
  (c y0 * d z18 - c y11 * d z8 = 0) ∧
  (c y0 * d z19 - c y11 * d z9 = 0)

theorem row_data_of_rows (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem
            (Complex.normSq (c y0)) (Complex.normSq (c y1)) (Complex.normSq (c y2)) (Complex.normSq (c y3)) (Complex.normSq (c y4)) (Complex.normSq (c y5)) (Complex.normSq (c y6)) (Complex.normSq (c y7)) (Complex.normSq (c y8)) (Complex.normSq (c y9)) (Complex.normSq (c y10)) (Complex.normSq (c y11)) (Complex.normSq (c y12)) (Complex.normSq (c y13)) (Complex.normSq (c y14)) (Complex.normSq (c y15)) (Complex.normSq (c y16)) (Complex.normSq (c y17)) (Complex.normSq (c y18)) (Complex.normSq (c y19)) (Complex.normSq (c y20)) (Complex.normSq (c y21))
            (Complex.normSq (d z0)) (Complex.normSq (d z1)) (Complex.normSq (d z2)) (Complex.normSq (d z3)) (Complex.normSq (d z4)) (Complex.normSq (d z5)) (Complex.normSq (d z6)) (Complex.normSq (d z7)) (Complex.normSq (d z8)) (Complex.normSq (d z9)) (Complex.normSq (d z10)) (Complex.normSq (d z11)) (Complex.normSq (d z12)) (Complex.normSq (d z13)) (Complex.normSq (d z14)) (Complex.normSq (d z15)) (Complex.normSq (d z16)) (Complex.normSq (d z17)) (Complex.normSq (d z18)) (Complex.normSq (d z19)))
    (ho0 : offSum c d ef0 w0 = 0)
    (ho1 : offSum c d ef0 w6 = 0)
    (ho2 : offSum c d ef1 w0 = 0)
    (ho3 : offSum c d ef1 w6 = 0)
    (ho4 : offSum c d ef0 w1 = 0)
    (ho5 : offSum c d ef0 w2 = 0)
    (ho6 : offSum c d ef0 w3 = 0)
    (ho7 : offSum c d ef0 w4 = 0)
    (ho8 : offSum c d ef2 w0 = 0)
    (ho9 : offSum c d ef2 w6 = 0)
    (ho10 : offSum c d ef3 w0 = 0)
    (ho11 : offSum c d ef3 w6 = 0)
    (ho12 : offSum c d ef2 w1 = 0)
    (ho13 : offSum c d ef2 w2 = 0)
    (ho14 : offSum c d ef2 w3 = 0)
    (ho15 : offSum c d ef2 w5 = 0)
    (ho16 : offSum c d ef4 w0 = 0)
    (ho17 : offSum c d ef4 w6 = 0)
    (ho18 : offSum c d ef5 w0 = 0)
    (ho19 : offSum c d ef5 w6 = 0)
    (ho20 : offSum c d ef4 w1 = 0)
    (ho21 : offSum c d ef4 w2 = 0)
    (ho22 : offSum c d ef4 w4 = 0)
    (ho23 : offSum c d ef4 w5 = 0)
    (ho24 : offSum c d ef6 w0 = 0)
    (ho25 : offSum c d ef6 w6 = 0)
    (ho26 : offSum c d ef7 w0 = 0)
    (ho27 : offSum c d ef7 w6 = 0)
    (ho28 : offSum c d ef6 w1 = 0)
    (ho29 : offSum c d ef6 w3 = 0)
    (ho30 : offSum c d ef6 w4 = 0)
    (ho31 : offSum c d ef6 w5 = 0)
    (ho32 : offSum c d ef8 w0 = 0)
    (ho33 : offSum c d ef8 w6 = 0)
    (ho34 : offSum c d ef9 w0 = 0)
    (ho35 : offSum c d ef9 w6 = 0)
    (ho36 : offSum c d ef8 w2 = 0)
    (ho37 : offSum c d ef8 w3 = 0)
    (ho38 : offSum c d ef8 w4 = 0)
    (ho39 : offSum c d ef8 w5 = 0)
    (hd0 : diagBot c efA w0 = diagTop d efA w0)
    (hd1 : diagBot c efA w6 = diagTop d efA w6)
    : RowData c d := by
  rw [ex_ef0_w0] at ho0
  rw [ex_ef0_w6] at ho1
  rw [ex_ef1_w0] at ho2
  rw [ex_ef1_w6] at ho3
  rw [ex_ef0_w1] at ho4
  rw [ex_ef0_w2] at ho5
  rw [ex_ef0_w3] at ho6
  rw [ex_ef0_w4] at ho7
  rw [ex_ef2_w0] at ho8
  rw [ex_ef2_w6] at ho9
  rw [ex_ef3_w0] at ho10
  rw [ex_ef3_w6] at ho11
  rw [ex_ef2_w1] at ho12
  rw [ex_ef2_w2] at ho13
  rw [ex_ef2_w3] at ho14
  rw [ex_ef2_w5] at ho15
  rw [ex_ef4_w0] at ho16
  rw [ex_ef4_w6] at ho17
  rw [ex_ef5_w0] at ho18
  rw [ex_ef5_w6] at ho19
  rw [ex_ef4_w1] at ho20
  rw [ex_ef4_w2] at ho21
  rw [ex_ef4_w4] at ho22
  rw [ex_ef4_w5] at ho23
  rw [ex_ef6_w0] at ho24
  rw [ex_ef6_w6] at ho25
  rw [ex_ef7_w0] at ho26
  rw [ex_ef7_w6] at ho27
  rw [ex_ef6_w1] at ho28
  rw [ex_ef6_w3] at ho29
  rw [ex_ef6_w4] at ho30
  rw [ex_ef6_w5] at ho31
  rw [ex_ef8_w0] at ho32
  rw [ex_ef8_w6] at ho33
  rw [ex_ef9_w0] at ho34
  rw [ex_ef9_w6] at ho35
  rw [ex_ef8_w2] at ho36
  rw [ex_ef8_w3] at ho37
  rw [ex_ef8_w4] at ho38
  rw [ex_ef8_w5] at ho39
  rw [dexB_w0, dexT_w0] at hd0
  rw [dexB_w6, dexT_w6] at hd1
  obtain ⟨hR, hC, hB, hA0, hA1⟩ := hm.facts
  have hP1 : star (c y0) * d z5 + star (c y11) * d z15 = 0 := by
    linear_combination (1/3 : ℂ) * ho0 + (1/6 : ℂ) * ho4 + (1/6 : ℂ) * ho5 + (1/6 : ℂ) * ho6 + (1/6 : ℂ) * ho7
  have nP1 : Complex.normSq (star (c y0) * d z5 + star (c y11) * d z15) = 0 := by
    rw [hP1]; simp
  have hP2 : star (c y0) * d z3 + star (c y11) * d z13 = 0 := by
    linear_combination (1/3 : ℂ) * ho8 + (1/6 : ℂ) * ho12 + (1/6 : ℂ) * ho13 + (1/6 : ℂ) * ho14 + (1/6 : ℂ) * ho15
  have nP2 : Complex.normSq (star (c y0) * d z3 + star (c y11) * d z13) = 0 := by
    rw [hP2]; simp
  have hP3 : star (c y0) * d z2 + star (c y11) * d z12 = 0 := by
    linear_combination (1/3 : ℂ) * ho16 + (1/6 : ℂ) * ho20 + (1/6 : ℂ) * ho21 + (1/6 : ℂ) * ho22 + (1/6 : ℂ) * ho23
  have nP3 : Complex.normSq (star (c y0) * d z2 + star (c y11) * d z12) = 0 := by
    rw [hP3]; simp
  have hP4 : star (c y0) * d z1 + star (c y11) * d z11 = 0 := by
    linear_combination (1/3 : ℂ) * ho24 + (1/6 : ℂ) * ho28 + (1/6 : ℂ) * ho29 + (1/6 : ℂ) * ho30 + (1/6 : ℂ) * ho31
  have nP4 : Complex.normSq (star (c y0) * d z1 + star (c y11) * d z11) = 0 := by
    rw [hP4]; simp
  have hP5 : star (c y0) * d z0 + star (c y11) * d z10 = 0 := by
    linear_combination (1/3 : ℂ) * ho32 + (1/6 : ℂ) * ho36 + (1/6 : ℂ) * ho37 + (1/6 : ℂ) * ho38 + (1/6 : ℂ) * ho39
  have nP5 : Complex.normSq (star (c y0) * d z0 + star (c y11) * d z10) = 0 := by
    rw [hP5]; simp
  have Roff : star (c y11) * c y0 + star (c y12) * c y1 + star (c y13) * c y2 + star (c y14) * c y3 + star (c y15) * c y4 + star (c y16) * c y5 + star (c y17) * c y6 + star (c y18) * c y7 + star (c y19) * c y8 + star (c y20) * c y9 + star (c y21) * c y10
      = star (d z15) * d z5 + star (d z13) * d z3 + star (d z12) * d z2 + star (d z11) * d z1 + star (d z10) * d z0 + star (d z14) * d z4 + star (d z16) * d z6 + star (d z17) * d z7 + star (d z18) * d z8 + star (d z19) * d z9 := by
    linear_combination (1/2 : ℂ) * hd0 + (1/2 : ℂ) * hd1
  have Rofs : star (c y0) * c y11 + star (c y1) * c y12 + star (c y2) * c y13 + star (c y3) * c y14 + star (c y4) * c y15 + star (c y5) * c y16 + star (c y6) * c y17 + star (c y7) * c y18 + star (c y8) * c y19 + star (c y9) * c y20 + star (c y10) * c y21
      = star (d z5) * d z15 + star (d z3) * d z13 + star (d z2) * d z12 + star (d z1) * d z11 + star (d z0) * d z10 + star (d z4) * d z14 + star (d z6) * d z16 + star (d z7) * d z17 + star (d z8) * d z18 + star (d z9) * d z19 := by
    linear_combination (1/2 : ℂ) * hd0 + (-1/2 : ℂ) * hd1
  have Rc00 : star (c y0) * c y0 + star (c y1) * c y1 + star (c y2) * c y2 + star (c y3) * c y3 + star (c y4) * c y4 + star (c y5) * c y5 + star (c y6) * c y6 + star (c y7) * c y7 + star (c y8) * c y8 + star (c y9) * c y9 + star (c y10) * c y10
      = star (d z5) * d z5 + star (d z3) * d z3 + star (d z2) * d z2 + star (d z1) * d z1 + star (d z0) * d z0 + star (d z4) * d z4 + star (d z6) * d z6 + star (d z7) * d z7 + star (d z8) * d z8 + star (d z9) * d z9 := by
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hA0
    push_cast at hc
    simp only [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have Rc11 : star (c y11) * c y11 + star (c y12) * c y12 + star (c y13) * c y13 + star (c y14) * c y14 + star (c y15) * c y15 + star (c y16) * c y16 + star (c y17) * c y17 + star (c y18) * c y18 + star (c y19) * c y19 + star (c y20) * c y20 + star (c y21) * c y21
      = star (d z15) * d z15 + star (d z13) * d z13 + star (d z12) * d z12 + star (d z11) * d z11 + star (d z10) * d z10 + star (d z14) * d z14 + star (d z16) * d z16 + star (d z17) * d z17 + star (d z18) * d z18 + star (d z19) * d z19 := by
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hA1
    push_cast at hc
    simp only [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have main :
      (c y0 * star (c y0) + c y11 * star (c y11)) * (star (c y0) * c y0 + star (c y11) * c y11)
        + (c y1 * star (c y0) + c y12 * star (c y11)) * (star (c y1) * c y0 + star (c y12) * c y11)
        + (c y2 * star (c y0) + c y13 * star (c y11)) * (star (c y2) * c y0 + star (c y13) * c y11)
        + (c y3 * star (c y0) + c y14 * star (c y11)) * (star (c y3) * c y0 + star (c y14) * c y11)
        + (c y4 * star (c y0) + c y15 * star (c y11)) * (star (c y4) * c y0 + star (c y15) * c y11)
        + (c y5 * star (c y0) + c y16 * star (c y11)) * (star (c y5) * c y0 + star (c y16) * c y11)
        + (c y6 * star (c y0) + c y17 * star (c y11)) * (star (c y6) * c y0 + star (c y17) * c y11)
        + (c y7 * star (c y0) + c y18 * star (c y11)) * (star (c y7) * c y0 + star (c y18) * c y11)
        + (c y8 * star (c y0) + c y19 * star (c y11)) * (star (c y8) * c y0 + star (c y19) * c y11)
        + (c y9 * star (c y0) + c y20 * star (c y11)) * (star (c y9) * c y0 + star (c y20) * c y11)
        + (c y10 * star (c y0) + c y21 * star (c y11)) * (star (c y10) * c y0 + star (c y21) * c y11)
      = (c y0 * star (d z5) + c y11 * star (d z15)) * (star (c y0) * d z5 + star (c y11) * d z15)
        + (c y0 * star (d z3) + c y11 * star (d z13)) * (star (c y0) * d z3 + star (c y11) * d z13)
        + (c y0 * star (d z2) + c y11 * star (d z12)) * (star (c y0) * d z2 + star (c y11) * d z12)
        + (c y0 * star (d z1) + c y11 * star (d z11)) * (star (c y0) * d z1 + star (c y11) * d z11)
        + (c y0 * star (d z0) + c y11 * star (d z10)) * (star (c y0) * d z0 + star (c y11) * d z10)
        + (c y0 * star (d z4) + c y11 * star (d z14)) * (star (c y0) * d z4 + star (c y11) * d z14)
        + (c y0 * star (d z6) + c y11 * star (d z16)) * (star (c y0) * d z6 + star (c y11) * d z16)
        + (c y0 * star (d z7) + c y11 * star (d z17)) * (star (c y0) * d z7 + star (c y11) * d z17)
        + (c y0 * star (d z8) + c y11 * star (d z18)) * (star (c y0) * d z8 + star (c y11) * d z18)
        + (c y0 * star (d z9) + c y11 * star (d z19)) * (star (c y0) * d z9 + star (c y11) * d z19) := by
    linear_combination (star (c y0) * c y0) * Rc00 + (star (c y11) * c y11) * Rc11
      + (star (c y0) * c y11) * Roff + (star (c y11) * c y0) * Rofs
  have hreal :
      (Complex.normSq (c y0) + Complex.normSq (c y11)) * (Complex.normSq (c y0) + Complex.normSq (c y11))
        + Complex.normSq (star (c y1) * c y0 + star (c y12) * c y11)
        + Complex.normSq (star (c y2) * c y0 + star (c y13) * c y11)
        + Complex.normSq (star (c y3) * c y0 + star (c y14) * c y11)
        + Complex.normSq (star (c y4) * c y0 + star (c y15) * c y11)
        + Complex.normSq (star (c y5) * c y0 + star (c y16) * c y11)
        + Complex.normSq (star (c y6) * c y0 + star (c y17) * c y11)
        + Complex.normSq (star (c y7) * c y0 + star (c y18) * c y11)
        + Complex.normSq (star (c y8) * c y0 + star (c y19) * c y11)
        + Complex.normSq (star (c y9) * c y0 + star (c y20) * c y11)
        + Complex.normSq (star (c y10) * c y0 + star (c y21) * c y11)
      = Complex.normSq (star (c y0) * d z5 + star (c y11) * d z15)
        + Complex.normSq (star (c y0) * d z3 + star (c y11) * d z13)
        + Complex.normSq (star (c y0) * d z2 + star (c y11) * d z12)
        + Complex.normSq (star (c y0) * d z1 + star (c y11) * d z11)
        + Complex.normSq (star (c y0) * d z0 + star (c y11) * d z10)
        + Complex.normSq (star (c y0) * d z4 + star (c y11) * d z14)
        + Complex.normSq (star (c y0) * d z6 + star (c y11) * d z16)
        + Complex.normSq (star (c y0) * d z7 + star (c y11) * d z17)
        + Complex.normSq (star (c y0) * d z8 + star (c y11) * d z18)
        + Complex.normSq (star (c y0) * d z9 + star (c y11) * d z19) := by
    have hc : (((Complex.normSq (c y0) + Complex.normSq (c y11)) * (Complex.normSq (c y0) + Complex.normSq (c y11)) + Complex.normSq (star (c y1) * c y0 + star (c y12) * c y11) + Complex.normSq (star (c y2) * c y0 + star (c y13) * c y11) + Complex.normSq (star (c y3) * c y0 + star (c y14) * c y11) + Complex.normSq (star (c y4) * c y0 + star (c y15) * c y11) + Complex.normSq (star (c y5) * c y0 + star (c y16) * c y11) + Complex.normSq (star (c y6) * c y0 + star (c y17) * c y11) + Complex.normSq (star (c y7) * c y0 + star (c y18) * c y11) + Complex.normSq (star (c y8) * c y0 + star (c y19) * c y11) + Complex.normSq (star (c y9) * c y0 + star (c y20) * c y11) + Complex.normSq (star (c y10) * c y0 + star (c y21) * c y11) : ℝ) : ℂ)
        = ((Complex.normSq (star (c y0) * d z5 + star (c y11) * d z15) + Complex.normSq (star (c y0) * d z3 + star (c y11) * d z13) + Complex.normSq (star (c y0) * d z2 + star (c y11) * d z12) + Complex.normSq (star (c y0) * d z1 + star (c y11) * d z11) + Complex.normSq (star (c y0) * d z0 + star (c y11) * d z10) + Complex.normSq (star (c y0) * d z4 + star (c y11) * d z14) + Complex.normSq (star (c y0) * d z6 + star (c y11) * d z16) + Complex.normSq (star (c y0) * d z7 + star (c y11) * d z17) + Complex.normSq (star (c y0) * d z8 + star (c y11) * d z18) + Complex.normSq (star (c y0) * d z9 + star (c y11) * d z19) : ℝ) : ℂ) := by
      push_cast
      simp only [← SixQubit.star_mul_self, star_add, star_mul', star_star]
      linear_combination main
    exact_mod_cast hc
  rw [hR] at hreal
  have hL1 := SixQubit.Spinor.lagrange (c y0) (c y11) (d z4) (d z14)
  rw [hR] at hL1
  have hL2 := SixQubit.Spinor.lagrange (c y0) (c y11) (d z6) (d z16)
  rw [hR] at hL2
  have hL3 := SixQubit.Spinor.lagrange (c y0) (c y11) (d z7) (d z17)
  rw [hR] at hL3
  have hL4 := SixQubit.Spinor.lagrange (c y0) (c y11) (d z8) (d z18)
  rw [hR] at hL4
  have hL5 := SixQubit.Spinor.lagrange (c y0) (c y11) (d z9) (d z19)
  rw [hR] at hL5
  have hz :
      Complex.normSq (star (c y1) * c y0 + star (c y12) * c y11)
        + Complex.normSq (star (c y2) * c y0 + star (c y13) * c y11)
        + Complex.normSq (star (c y3) * c y0 + star (c y14) * c y11)
        + Complex.normSq (star (c y4) * c y0 + star (c y15) * c y11)
        + Complex.normSq (star (c y5) * c y0 + star (c y16) * c y11)
        + Complex.normSq (star (c y6) * c y0 + star (c y17) * c y11)
        + Complex.normSq (star (c y7) * c y0 + star (c y18) * c y11)
        + Complex.normSq (star (c y8) * c y0 + star (c y19) * c y11)
        + Complex.normSq (star (c y9) * c y0 + star (c y20) * c y11)
        + Complex.normSq (star (c y10) * c y0 + star (c y21) * c y11)
        + Complex.normSq (c y0 * d z14 - c y11 * d z4)
        + Complex.normSq (c y0 * d z16 - c y11 * d z6)
        + Complex.normSq (c y0 * d z17 - c y11 * d z7)
        + Complex.normSq (c y0 * d z18 - c y11 * d z8)
        + Complex.normSq (c y0 * d z19 - c y11 * d z9)
      = 0 := by
    linarith only [hreal, hC, hL1, hL2, hL3, hL4, hL5, nP1, nP2, nP3, nP4, nP5]
  have ha0 : star (c y1) * c y0 + star (c y12) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have ha1 : star (c y2) * c y0 + star (c y13) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have ha2 : star (c y3) * c y0 + star (c y14) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have ha3 : star (c y4) * c y0 + star (c y15) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have ha4 : star (c y5) * c y0 + star (c y16) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have ha5 : star (c y6) * c y0 + star (c y17) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have ha6 : star (c y7) * c y0 + star (c y18) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have ha7 : star (c y8) * c y0 + star (c y19) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have ha8 : star (c y9) * c y0 + star (c y20) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have ha9 : star (c y10) * c y0 + star (c y21) * c y11 = 0 :=
    Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have hS : star (c y0) * c y0 + star (c y11) * c y11 = (1/3 : ℂ) := by
    have hc := congrArg (fun x : ℝ => (x : ℂ)) hR
    push_cast at hc
    simp only [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have E1_00 : star (c y0) * d z5
      + star (c y1) * d z6
      + star (c y2) * d z7
      + star (c y3) * d z8
      + star (c y4) * d z9
      = 0 := by
    linear_combination (1/2 : ℂ) * ho0 + (1/2 : ℂ) * ho1
  have E1_10 : star (c y11) * d z5
      + star (c y12) * d z6
      + star (c y13) * d z7
      + star (c y14) * d z8
      + star (c y15) * d z9
      = 0 := by
    linear_combination (1/2 : ℂ) * ho2 + (1/2 : ℂ) * ho3
  have E1_01 : star (c y0) * d z15
      + star (c y1) * d z16
      + star (c y2) * d z17
      + star (c y3) * d z18
      + star (c y4) * d z19
      = 0 := by
    linear_combination (1/2 : ℂ) * ho2 + (-1/2 : ℂ) * ho3
  have E1_11 : star (c y11) * d z15
      + star (c y12) * d z16
      + star (c y13) * d z17
      + star (c y14) * d z18
      + star (c y15) * d z19
      = 0 := by
    linear_combination (1/2 : ℂ) * ho0 + (-1/2 : ℂ) * ho1
  have E2_00 : star (c y0) * d z3
      + star (c y1) * d z4
      + star (c y5) * d z7
      + star (c y6) * d z8
      + star (c y7) * d z9
      = 0 := by
    linear_combination (1/2 : ℂ) * ho8 + (1/2 : ℂ) * ho9
  have E2_10 : star (c y11) * d z3
      + star (c y12) * d z4
      + star (c y16) * d z7
      + star (c y17) * d z8
      + star (c y18) * d z9
      = 0 := by
    linear_combination (1/2 : ℂ) * ho10 + (1/2 : ℂ) * ho11
  have E2_01 : star (c y0) * d z13
      + star (c y1) * d z14
      + star (c y5) * d z17
      + star (c y6) * d z18
      + star (c y7) * d z19
      = 0 := by
    linear_combination (1/2 : ℂ) * ho10 + (-1/2 : ℂ) * ho11
  have E2_11 : star (c y11) * d z13
      + star (c y12) * d z14
      + star (c y16) * d z17
      + star (c y17) * d z18
      + star (c y18) * d z19
      = 0 := by
    linear_combination (1/2 : ℂ) * ho8 + (-1/2 : ℂ) * ho9
  have E3_00 : star (c y0) * d z2
      + star (c y2) * d z4
      + star (c y5) * d z6
      + star (c y8) * d z8
      + star (c y9) * d z9
      = 0 := by
    linear_combination (1/2 : ℂ) * ho16 + (1/2 : ℂ) * ho17
  have E3_10 : star (c y11) * d z2
      + star (c y13) * d z4
      + star (c y16) * d z6
      + star (c y19) * d z8
      + star (c y20) * d z9
      = 0 := by
    linear_combination (1/2 : ℂ) * ho18 + (1/2 : ℂ) * ho19
  have E3_01 : star (c y0) * d z12
      + star (c y2) * d z14
      + star (c y5) * d z16
      + star (c y8) * d z18
      + star (c y9) * d z19
      = 0 := by
    linear_combination (1/2 : ℂ) * ho18 + (-1/2 : ℂ) * ho19
  have E3_11 : star (c y11) * d z12
      + star (c y13) * d z14
      + star (c y16) * d z16
      + star (c y19) * d z18
      + star (c y20) * d z19
      = 0 := by
    linear_combination (1/2 : ℂ) * ho16 + (-1/2 : ℂ) * ho17
  have E4_00 : star (c y0) * d z1
      + star (c y3) * d z4
      + star (c y6) * d z6
      + star (c y8) * d z7
      + star (c y10) * d z9
      = 0 := by
    linear_combination (1/2 : ℂ) * ho24 + (1/2 : ℂ) * ho25
  have E4_10 : star (c y11) * d z1
      + star (c y14) * d z4
      + star (c y17) * d z6
      + star (c y19) * d z7
      + star (c y21) * d z9
      = 0 := by
    linear_combination (1/2 : ℂ) * ho26 + (1/2 : ℂ) * ho27
  have E4_01 : star (c y0) * d z11
      + star (c y3) * d z14
      + star (c y6) * d z16
      + star (c y8) * d z17
      + star (c y10) * d z19
      = 0 := by
    linear_combination (1/2 : ℂ) * ho26 + (-1/2 : ℂ) * ho27
  have E4_11 : star (c y11) * d z11
      + star (c y14) * d z14
      + star (c y17) * d z16
      + star (c y19) * d z17
      + star (c y21) * d z19
      = 0 := by
    linear_combination (1/2 : ℂ) * ho24 + (-1/2 : ℂ) * ho25
  have E5_00 : star (c y0) * d z0
      + star (c y4) * d z4
      + star (c y7) * d z6
      + star (c y9) * d z7
      + star (c y10) * d z8
      = 0 := by
    linear_combination (1/2 : ℂ) * ho32 + (1/2 : ℂ) * ho33
  have E5_10 : star (c y11) * d z0
      + star (c y15) * d z4
      + star (c y18) * d z6
      + star (c y20) * d z7
      + star (c y21) * d z8
      = 0 := by
    linear_combination (1/2 : ℂ) * ho34 + (1/2 : ℂ) * ho35
  have E5_01 : star (c y0) * d z10
      + star (c y4) * d z14
      + star (c y7) * d z16
      + star (c y9) * d z17
      + star (c y10) * d z18
      = 0 := by
    linear_combination (1/2 : ℂ) * ho34 + (-1/2 : ℂ) * ho35
  have E5_11 : star (c y11) * d z10
      + star (c y15) * d z14
      + star (c y18) * d z16
      + star (c y20) * d z17
      + star (c y21) * d z18
      = 0 := by
    linear_combination (1/2 : ℂ) * ho32 + (-1/2 : ℂ) * ho33
  have wc0 : c y0 * d z14 - c y11 * d z4 = 0 := Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have wc1 : c y0 * d z16 - c y11 * d z6 = 0 := Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have wc2 : c y0 * d z17 - c y11 * d z7 = 0 := Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have wc3 : c y0 * d z18 - c y11 * d z8 = 0 := Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  have wc4 : c y0 * d z19 - c y11 * d z9 = 0 := Complex.normSq_eq_zero.mp (by linarith only [hz, Complex.normSq_nonneg (star (c y1) * c y0 + star (c y12) * c y11), Complex.normSq_nonneg (star (c y2) * c y0 + star (c y13) * c y11), Complex.normSq_nonneg (star (c y3) * c y0 + star (c y14) * c y11), Complex.normSq_nonneg (star (c y4) * c y0 + star (c y15) * c y11), Complex.normSq_nonneg (star (c y5) * c y0 + star (c y16) * c y11), Complex.normSq_nonneg (star (c y6) * c y0 + star (c y17) * c y11), Complex.normSq_nonneg (star (c y7) * c y0 + star (c y18) * c y11), Complex.normSq_nonneg (star (c y8) * c y0 + star (c y19) * c y11), Complex.normSq_nonneg (star (c y9) * c y0 + star (c y20) * c y11), Complex.normSq_nonneg (star (c y10) * c y0 + star (c y21) * c y11), Complex.normSq_nonneg (c y0 * d z14 - c y11 * d z4), Complex.normSq_nonneg (c y0 * d z16 - c y11 * d z6), Complex.normSq_nonneg (c y0 * d z17 - c y11 * d z7), Complex.normSq_nonneg (c y0 * d z18 - c y11 * d z8), Complex.normSq_nonneg (c y0 * d z19 - c y11 * d z9)])
  exact ⟨hP1, hP2, hP3, hP4, hP5, Roff, Rofs, Rc00, Rc11, ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, E1_00, E1_01, E1_10, E1_11, E2_00, E2_01, E2_10, E2_11, E3_00, E3_01, E3_10, E3_11, E4_00, E4_01, E4_10, E4_11, E5_00, E5_01, E5_10, E5_11, hR, hC, hB, wc0, wc1, wc2, wc3, wc4⟩

theorem physical_row_data (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) : RowData c d :=
  row_data_of_rows c d
    (moments c d hc hd hnc hnd hdist)
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w6 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef1 w6 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w3 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef0 w4 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef2 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef2 w6 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef3 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef3 w6 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef2 w1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef2 w2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef2 w3 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef2 w5 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef4 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef4 w6 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef5 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef5 w6 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef4 w1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef4 w2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef4 w4 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef4 w5 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef6 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef6 w6 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef7 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef7 w6 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef6 w1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef6 w3 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef6 w4 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef6 w5 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef8 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef8 w6 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef9 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef9 w6 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef8 w2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef8 w3 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef8 w4 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      ef8 w5 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      efA w0 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      efA w6 (by decide))


end
end MainTheory.Orbit6PhysicalRowData
