import SixQubit.CodeOrbit5
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
namespace MainTheory.Orbit5PhysicalRowData
open scoped BigOperators Matrix
open SixQubit SixQubit.Orbit5
noncomputable section

def RowData (c d : SS.State 6 ℂ) : Prop :=
  (Trace5.nsq (uu c) = 1/3) ∧
  (Trace5.nsq (vv d) = 1/3) ∧
  (Trace5.nsq (aa1 c) = 1/6) ∧
  (Trace5.nsq (aa2 c) = 1/6) ∧
  (Trace5.nsq (aa3 c) = 1/6) ∧
  (Trace5.nsq (aa4 c) = 1/6) ∧
  (Trace5.nsq (bb1 d) = 1/6) ∧
  (Trace5.nsq (bb2 d) = 1/6) ∧
  (Trace5.nsq (bb3 d) = 1/6) ∧
  (Trace5.nsq (bb4 d) = 1/6) ∧
  (Trace5.ip (uu c) (bb1 d) = 0) ∧
  (Trace5.ip (uu c) (bb2 d) = 0) ∧
  (Trace5.ip (uu c) (bb3 d) = 0) ∧
  (Trace5.ip (uu c) (bb4 d) = 0) ∧
  (∀ k l : Fin 4, uu c k * star (uu c l)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) k l
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) k l + vv d k * star (vv d l)) ∧
  (Trace5.ip (aa1 c) (bb2 d) + Trace5.ip (aa2 c) (bb1 d) = 0) ∧
  (Trace5.ip (aa1 c) (bb3 d) + Trace5.ip (aa3 c) (bb1 d) = 0) ∧
  (Trace5.ip (aa1 c) (bb4 d) + Trace5.ip (aa4 c) (bb1 d) = 0) ∧
  (Trace5.ip (aa2 c) (bb3 d) + Trace5.ip (aa3 c) (bb2 d) = 0) ∧
  (Trace5.ip (aa2 c) (bb4 d) + Trace5.ip (aa4 c) (bb2 d) = 0) ∧
  (Trace5.ip (aa3 c) (bb4 d) + Trace5.ip (aa4 c) (bb3 d) = 0) ∧
  (star (uu c 0) * bb1 d 0 + star (uu c 1) * bb1 d 1 + star (aa1 c 0) * vv d 0
      + star (aa1 c 1) * vv d 1 = 0) ∧
  (star (uu c 2) * bb1 d 0 + star (uu c 3) * bb1 d 1 + star (aa1 c 2) * vv d 0
      + star (aa1 c 3) * vv d 1 = 0) ∧
  (star (uu c 0) * bb1 d 2 + star (uu c 1) * bb1 d 3 + star (aa1 c 0) * vv d 2
      + star (aa1 c 1) * vv d 3 = 0) ∧
  (star (uu c 2) * bb1 d 2 + star (uu c 3) * bb1 d 3 + star (aa1 c 2) * vv d 2
      + star (aa1 c 3) * vv d 3 = 0) ∧
  (star (uu c 0) * bb1 d 0 + star (uu c 2) * bb1 d 2 + star (aa1 c 0) * vv d 0
      + star (aa1 c 2) * vv d 2 = 0) ∧
  (star (uu c 1) * bb1 d 0 + star (uu c 3) * bb1 d 2 + star (aa1 c 1) * vv d 0
      + star (aa1 c 3) * vv d 2 = 0) ∧
  (star (uu c 0) * bb1 d 1 + star (uu c 2) * bb1 d 3 + star (aa1 c 0) * vv d 1
      + star (aa1 c 2) * vv d 3 = 0) ∧
  (star (uu c 1) * bb1 d 1 + star (uu c 3) * bb1 d 3 + star (aa1 c 1) * vv d 1
      + star (aa1 c 3) * vv d 3 = 0) ∧
  (star (uu c 0) * bb2 d 0 + star (uu c 1) * bb2 d 1 + star (aa2 c 0) * vv d 0
      + star (aa2 c 1) * vv d 1 = 0) ∧
  (star (uu c 2) * bb2 d 0 + star (uu c 3) * bb2 d 1 + star (aa2 c 2) * vv d 0
      + star (aa2 c 3) * vv d 1 = 0) ∧
  (star (uu c 0) * bb2 d 2 + star (uu c 1) * bb2 d 3 + star (aa2 c 0) * vv d 2
      + star (aa2 c 1) * vv d 3 = 0) ∧
  (star (uu c 2) * bb2 d 2 + star (uu c 3) * bb2 d 3 + star (aa2 c 2) * vv d 2
      + star (aa2 c 3) * vv d 3 = 0) ∧
  (star (uu c 0) * bb2 d 0 + star (uu c 2) * bb2 d 2 + star (aa2 c 0) * vv d 0
      + star (aa2 c 2) * vv d 2 = 0) ∧
  (star (uu c 1) * bb2 d 0 + star (uu c 3) * bb2 d 2 + star (aa2 c 1) * vv d 0
      + star (aa2 c 3) * vv d 2 = 0) ∧
  (star (uu c 0) * bb2 d 1 + star (uu c 2) * bb2 d 3 + star (aa2 c 0) * vv d 1
      + star (aa2 c 2) * vv d 3 = 0) ∧
  (star (uu c 1) * bb2 d 1 + star (uu c 3) * bb2 d 3 + star (aa2 c 1) * vv d 1
      + star (aa2 c 3) * vv d 3 = 0) ∧
  (star (uu c 0) * bb3 d 0 + star (uu c 1) * bb3 d 1 + star (aa3 c 0) * vv d 0
      + star (aa3 c 1) * vv d 1 = 0) ∧
  (star (uu c 2) * bb3 d 0 + star (uu c 3) * bb3 d 1 + star (aa3 c 2) * vv d 0
      + star (aa3 c 3) * vv d 1 = 0) ∧
  (star (uu c 0) * bb3 d 2 + star (uu c 1) * bb3 d 3 + star (aa3 c 0) * vv d 2
      + star (aa3 c 1) * vv d 3 = 0) ∧
  (star (uu c 2) * bb3 d 2 + star (uu c 3) * bb3 d 3 + star (aa3 c 2) * vv d 2
      + star (aa3 c 3) * vv d 3 = 0) ∧
  (star (uu c 0) * bb3 d 0 + star (uu c 2) * bb3 d 2 + star (aa3 c 0) * vv d 0
      + star (aa3 c 2) * vv d 2 = 0) ∧
  (star (uu c 1) * bb3 d 0 + star (uu c 3) * bb3 d 2 + star (aa3 c 1) * vv d 0
      + star (aa3 c 3) * vv d 2 = 0) ∧
  (star (uu c 0) * bb3 d 1 + star (uu c 2) * bb3 d 3 + star (aa3 c 0) * vv d 1
      + star (aa3 c 2) * vv d 3 = 0) ∧
  (star (uu c 1) * bb3 d 1 + star (uu c 3) * bb3 d 3 + star (aa3 c 1) * vv d 1
      + star (aa3 c 3) * vv d 3 = 0) ∧
  (star (uu c 0) * bb4 d 0 + star (uu c 1) * bb4 d 1 + star (aa4 c 0) * vv d 0
      + star (aa4 c 1) * vv d 1 = 0) ∧
  (star (uu c 2) * bb4 d 0 + star (uu c 3) * bb4 d 1 + star (aa4 c 2) * vv d 0
      + star (aa4 c 3) * vv d 1 = 0) ∧
  (star (uu c 0) * bb4 d 2 + star (uu c 1) * bb4 d 3 + star (aa4 c 0) * vv d 2
      + star (aa4 c 1) * vv d 3 = 0) ∧
  (star (uu c 2) * bb4 d 2 + star (uu c 3) * bb4 d 3 + star (aa4 c 2) * vv d 2
      + star (aa4 c 3) * vv d 3 = 0) ∧
  (star (uu c 0) * bb4 d 0 + star (uu c 2) * bb4 d 2 + star (aa4 c 0) * vv d 0
      + star (aa4 c 2) * vv d 2 = 0) ∧
  (star (uu c 1) * bb4 d 0 + star (uu c 3) * bb4 d 2 + star (aa4 c 1) * vv d 0
      + star (aa4 c 3) * vv d 2 = 0) ∧
  (star (uu c 0) * bb4 d 1 + star (uu c 2) * bb4 d 3 + star (aa4 c 0) * vv d 1
      + star (aa4 c 2) * vv d 3 = 0) ∧
  (star (uu c 1) * bb4 d 1 + star (uu c 3) * bb4 d 3 + star (aa4 c 1) * vv d 1
      + star (aa4 c 3) * vv d 3 = 0)

theorem row_data_of_rows (c d : SS.BitString 6 -> ℂ)
    (hm : MomentSystem (Complex.normSq  (c  y0))  (Complex.normSq  (c  y1))  (Complex.normSq  (c  y2))
       (Complex.normSq  (c  y3))  (Complex.normSq  (c  y4))  (Complex.normSq  (c  y5))  (Complex.normSq
       (c  y6))  (Complex.normSq  (c  y7))  (Complex.normSq  (c  y8))  (Complex.normSq  (c  y9))
       (Complex.normSq  (c  y10))  (Complex.normSq  (c  y11))  (Complex.normSq  (c  y12))
       (Complex.normSq  (c  y13))  (Complex.normSq  (c  y14))  (Complex.normSq  (c  y15))
       (Complex.normSq  (c  y16))  (Complex.normSq  (c  y17))  (Complex.normSq  (c  y18))
       (Complex.normSq  (c  y19))  (Complex.normSq  (d  z0))  (Complex.normSq  (d  z1))  (Complex.normSq
       (d  z2))  (Complex.normSq  (d  z3))  (Complex.normSq  (d  z4))  (Complex.normSq  (d  z5))
       (Complex.normSq  (d  z6))  (Complex.normSq  (d  z7))  (Complex.normSq  (d  z8))  (Complex.normSq
       (d  z9))  (Complex.normSq  (d  z10))  (Complex.normSq  (d  z11))  (Complex.normSq  (d  z12))
       (Complex.normSq  (d  z13))  (Complex.normSq  (d  z14))  (Complex.normSq  (d  z15))
       (Complex.normSq  (d  z16))  (Complex.normSq  (d  z17))  (Complex.normSq  (d  z18))
       (Complex.normSq  (d  z19)))
    (ho1a : offSum c d f1 w0 = 0)
    (ho1b : offSum c d f1 f2 = 0)
    (ho2a : offSum c d f2 w0 = 0)
    (ho2b : offSum c d f2 f3 = 0)
    (ho3a : offSum c d f3 w0 = 0)
    (ho3b : offSum c d f3 f4 = 0)
    (ho4a : offSum c d f4 w0 = 0)
    (ho4b : offSum c d f4 f1 = 0)
    (hz11 : offSum c d f1 p1 = 0)
    (hz12 : offSum c d f1 p2 = 0)
    (hk10 : offSum c d k1 w0 = 0)
    (hk11 : offSum c d k1 p1 = 0)
    (hl10 : offSum c d l1 w0 = 0)
    (hl12 : offSum c d l1 p2 = 0)
    (hz21 : offSum c d f2 p1 = 0)
    (hz22 : offSum c d f2 p2 = 0)
    (hk20 : offSum c d k2 w0 = 0)
    (hk21 : offSum c d k2 p1 = 0)
    (hl20 : offSum c d l2 w0 = 0)
    (hl22 : offSum c d l2 p2 = 0)
    (hz31 : offSum c d f3 p1 = 0)
    (hz32 : offSum c d f3 p2 = 0)
    (hk30 : offSum c d k3 w0 = 0)
    (hk31 : offSum c d k3 p1 = 0)
    (hl30 : offSum c d l3 w0 = 0)
    (hl32 : offSum c d l3 p2 = 0)
    (hz41 : offSum c d f4 p1 = 0)
    (hz42 : offSum c d f4 p2 = 0)
    (hk40 : offSum c d k4 w0 = 0)
    (hk41 : offSum c d k4 p1 = 0)
    (hl40 : offSum c d l4 w0 = 0)
    (hl42 : offSum c d l4 p2 = 0)
    (ht12 : offSum c d g12 w0 = 0)
    (ht13 : offSum c d g13 w0 = 0)
    (ht14 : offSum c d g14 w0 = 0)
    (ht23 : offSum c d g23 w0 = 0)
    (ht24 : offSum c d g24 w0 = 0)
    (ht34 : offSum c d g34 w0 = 0)
    (hd11 : diagBot c p1 w0 = diagTop d p1 w0)
    (hd12 : diagBot c p1 w1 = diagTop d p1 w1)
    (hd13 : diagBot c p1 w2 = diagTop d p1 w2)
    (hd14 : diagBot c p1 w3 = diagTop d p1 w3)
    (hd21 : diagBot c p2 w0 = diagTop d p2 w0)
    (hd22 : diagBot c p2 w1 = diagTop d p2 w1)
    (hd23 : diagBot c p2 w2 = diagTop d p2 w2)
    (hd24 : diagBot c p2 w3 = diagTop d p2 w3)
    (hd31 : diagBot c p3 w0 = diagTop d p3 w0)
    (hd32 : diagBot c p3 w1 = diagTop d p3 w1)
    (hd33 : diagBot c p3 w2 = diagTop d p3 w2)
    (hd34 : diagBot c p3 w3 = diagTop d p3 w3)
    : RowData c d := by
  obtain ⟨nu, na1, na2, na3, na4, nb1, nb2, nb3, nb4, nv⟩ := hm.norms
  obtain ⟨mg0, mg1, mg2, mg3⟩ := hm.marginal
  have hnuu : Trace5.nsq (uu c) = 1/3 := by
    simp only [Trace5.nsq, uu_0, uu_1, uu_2, uu_3]
    linarith
  have hnaa1 : Trace5.nsq (aa1 c) = 1/6 := by
    simp only [Trace5.nsq, aa1_0, aa1_1, aa1_2, aa1_3]
    linarith
  have hnaa2 : Trace5.nsq (aa2 c) = 1/6 := by
    simp only [Trace5.nsq, aa2_0, aa2_1, aa2_2, aa2_3]
    linarith
  have hnaa3 : Trace5.nsq (aa3 c) = 1/6 := by
    simp only [Trace5.nsq, aa3_0, aa3_1, aa3_2, aa3_3]
    linarith
  have hnaa4 : Trace5.nsq (aa4 c) = 1/6 := by
    simp only [Trace5.nsq, aa4_0, aa4_1, aa4_2, aa4_3]
    linarith
  have hnbb1 : Trace5.nsq (bb1 d) = 1/6 := by
    simp only [Trace5.nsq, bb1_0, bb1_1, bb1_2, bb1_3]
    linarith
  have hnbb2 : Trace5.nsq (bb2 d) = 1/6 := by
    simp only [Trace5.nsq, bb2_0, bb2_1, bb2_2, bb2_3]
    linarith
  have hnbb3 : Trace5.nsq (bb3 d) = 1/6 := by
    simp only [Trace5.nsq, bb3_0, bb3_1, bb3_2, bb3_3]
    linarith
  have hnbb4 : Trace5.nsq (bb4 d) = 1/6 := by
    simp only [Trace5.nsq, bb4_0, bb4_1, bb4_2, bb4_3]
    linarith
  have hnvv : Trace5.nsq (vv d) = 1/3 := by
    simp only [Trace5.nsq, vv_0, vv_1, vv_2, vv_3]
    linarith
  have x12 : Trace5.ip (aa1 c) (bb2 d) + Trace5.ip (aa2 c) (bb1 d) = 0 := by
    linear_combination two_flip_12 c d ht12
  have x13 : Trace5.ip (aa1 c) (bb3 d) + Trace5.ip (aa3 c) (bb1 d) = 0 := by
    linear_combination two_flip_13 c d ht13
  have x14 : Trace5.ip (aa1 c) (bb4 d) + Trace5.ip (aa4 c) (bb1 d) = 0 := by
    linear_combination two_flip_14 c d ht14
  have x23 : Trace5.ip (aa2 c) (bb3 d) + Trace5.ip (aa3 c) (bb2 d) = 0 := by
    linear_combination two_flip_23 c d ht23
  have x24 : Trace5.ip (aa2 c) (bb4 d) + Trace5.ip (aa4 c) (bb2 d) = 0 := by
    linear_combination two_flip_24 c d ht24
  have x34 : Trace5.ip (aa3 c) (bb4 d) + Trace5.ip (aa4 c) (bb3 d) = 0 := by
    linear_combination two_flip_34 c d ht34
  rw [ex_f1_f2] at ho1b
  rw [ex_f2_f3] at ho2b
  rw [ex_f3_f4] at ho3b
  rw [ex_f4_f1] at ho4b
  rw [ex_f1_w0] at ho1a
  rw [ex_f1_p1] at hz11
  rw [ex_f1_p2] at hz12
  rw [ex_k1_w0] at hk10
  rw [ex_k1_p1] at hk11
  rw [ex_l1_w0] at hl10
  rw [ex_l1_p2] at hl12
  rw [ex_f2_w0] at ho2a
  rw [ex_f2_p1] at hz21
  rw [ex_f2_p2] at hz22
  rw [ex_k2_w0] at hk20
  rw [ex_k2_p1] at hk21
  rw [ex_l2_w0] at hl20
  rw [ex_l2_p2] at hl22
  rw [ex_f3_w0] at ho3a
  rw [ex_f3_p1] at hz31
  rw [ex_f3_p2] at hz32
  rw [ex_k3_w0] at hk30
  rw [ex_k3_p1] at hk31
  rw [ex_l3_w0] at hl30
  rw [ex_l3_p2] at hl32
  rw [ex_f4_w0] at ho4a
  rw [ex_f4_p1] at hz41
  rw [ex_f4_p2] at hz42
  rw [ex_k4_w0] at hk40
  rw [ex_k4_p1] at hk41
  rw [ex_l4_w0] at hl40
  rw [ex_l4_p2] at hl42
  have hq1 : Trace5.ip (uu c) (bb1 d) = 0 := by
    simp only [Trace5.ip, uu_0, uu_1, uu_2, uu_3, bb1_0, bb1_1, bb1_2, bb1_3]
    linear_combination (1/2 : ℂ) * ho1a + (1/2 : ℂ) * ho1b
  have hq2 : Trace5.ip (uu c) (bb2 d) = 0 := by
    simp only [Trace5.ip, uu_0, uu_1, uu_2, uu_3, bb2_0, bb2_1, bb2_2, bb2_3]
    linear_combination (1/2 : ℂ) * ho2a + (1/2 : ℂ) * ho2b
  have hq3 : Trace5.ip (uu c) (bb3 d) = 0 := by
    simp only [Trace5.ip, uu_0, uu_1, uu_2, uu_3, bb3_0, bb3_1, bb3_2, bb3_3]
    linear_combination (1/2 : ℂ) * ho3a + (1/2 : ℂ) * ho3b
  have hq4 : Trace5.ip (uu c) (bb4 d) = 0 := by
    simp only [Trace5.ip, uu_0, uu_1, uu_2, uu_3, bb4_0, bb4_1, bb4_2, bb4_3]
    linear_combination (1/2 : ℂ) * ho4a + (1/2 : ℂ) * ho4b
  rw [dexB_p1_w0, dexT_p1_w0] at hd11
  rw [dexB_p1_w1, dexT_p1_w1] at hd12
  rw [dexB_p1_w2, dexT_p1_w2] at hd13
  rw [dexB_p1_w3, dexT_p1_w3] at hd14
  rw [dexB_p2_w0, dexT_p2_w0] at hd21
  rw [dexB_p2_w1, dexT_p2_w1] at hd22
  rw [dexB_p2_w2, dexT_p2_w2] at hd23
  rw [dexB_p2_w3, dexT_p2_w3] at hd24
  rw [dexB_p3_w0, dexT_p3_w0] at hd31
  rw [dexB_p3_w1, dexT_p3_w1] at hd32
  rw [dexB_p3_w2, dexT_p3_w2] at hd33
  rw [dexB_p3_w3, dexT_p3_w3] at hd34
  have fk00 : uu c 0 * star (uu c 0)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 0 0
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 0 0
        + vv d 0 * star (vv d 0) := by
    simp only [Trace5.fr, uu_0, uu_0, aa1_0, aa2_0, aa3_0, aa4_0, aa1_0, aa2_0, aa3_0, aa4_0, vv_0, vv_0, bb1_0, bb2_0, bb3_0, bb4_0, bb1_0, bb2_0, bb3_0, bb4_0]
    have hc : ((Complex.normSq (c y0) + Complex.normSq (c y4) + Complex.normSq (c y8)
        + Complex.normSq (c y12) + Complex.normSq (c y16)
        : Real) : ℂ) = ((Complex.normSq (d z0) + Complex.normSq (d z4) + Complex.normSq (d z8)
        + Complex.normSq (d z12) + Complex.normSq (d z16) : Real) : ℂ) := by
      exact_mod_cast mg0
    push_cast [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have fk01 : uu c 0 * star (uu c 1)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 0 1
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 0 1
        + vv d 0 * star (vv d 1) := by
    simp only [Trace5.fr, uu_0, uu_1, aa1_0, aa2_0, aa3_0, aa4_0, aa1_1, aa2_1, aa3_1, aa4_1, vv_0, vv_1, bb1_0, bb2_0, bb3_0, bb4_0, bb1_1, bb2_1, bb3_1, bb4_1]
    linear_combination (1/4 : ℂ) * hd21 + (1/4 : ℂ) * hd22 + (1/4 : ℂ) * hd23 + (1/4 : ℂ) * hd24
  have fk02 : uu c 0 * star (uu c 2)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 0 2
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 0 2
        + vv d 0 * star (vv d 2) := by
    simp only [Trace5.fr, uu_0, uu_2, aa1_0, aa2_0, aa3_0, aa4_0, aa1_2, aa2_2, aa3_2, aa4_2, vv_0, vv_2, bb1_0, bb2_0, bb3_0, bb4_0, bb1_2, bb2_2, bb3_2, bb4_2]
    linear_combination (1/4 : ℂ) * hd11 + (1/4 : ℂ) * hd12 + (1/4 : ℂ) * hd13 + (1/4 : ℂ) * hd14
  have fk03 : uu c 0 * star (uu c 3)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 0 3
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 0 3
        + vv d 0 * star (vv d 3) := by
    simp only [Trace5.fr, uu_0, uu_3, aa1_0, aa2_0, aa3_0, aa4_0, aa1_3, aa2_3, aa3_3, aa4_3, vv_0, vv_3, bb1_0, bb2_0, bb3_0, bb4_0, bb1_3, bb2_3, bb3_3, bb4_3]
    linear_combination (1/4 : ℂ) * hd31 + (1/4 : ℂ) * hd32 + (1/4 : ℂ) * hd33 + (1/4 : ℂ) * hd34
  have fk10 : uu c 1 * star (uu c 0)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 1 0
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 1 0
        + vv d 1 * star (vv d 0) := by
    simp only [Trace5.fr, uu_1, uu_0, aa1_1, aa2_1, aa3_1, aa4_1, aa1_0, aa2_0, aa3_0, aa4_0, vv_1, vv_0, bb1_1, bb2_1, bb3_1, bb4_1, bb1_0, bb2_0, bb3_0, bb4_0]
    linear_combination (1/4 : ℂ) * hd21 + (1/4 : ℂ) * hd22 + (-1/4 : ℂ) * hd23 + (-1/4 : ℂ) * hd24
  have fk11 : uu c 1 * star (uu c 1)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 1 1
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 1 1
        + vv d 1 * star (vv d 1) := by
    simp only [Trace5.fr, uu_1, uu_1, aa1_1, aa2_1, aa3_1, aa4_1, aa1_1, aa2_1, aa3_1, aa4_1, vv_1, vv_1, bb1_1, bb2_1, bb3_1, bb4_1, bb1_1, bb2_1, bb3_1, bb4_1]
    have hc : ((Complex.normSq (c y1) + Complex.normSq (c y5) + Complex.normSq (c y9)
        + Complex.normSq (c y13) + Complex.normSq (c y17)
        : Real) : ℂ) = ((Complex.normSq (d z1) + Complex.normSq (d z5) + Complex.normSq (d z9)
        + Complex.normSq (d z13) + Complex.normSq (d z17) : Real) : ℂ) := by
      exact_mod_cast mg1
    push_cast [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have fk12 : uu c 1 * star (uu c 2)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 1 2
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 1 2
        + vv d 1 * star (vv d 2) := by
    simp only [Trace5.fr, uu_1, uu_2, aa1_1, aa2_1, aa3_1, aa4_1, aa1_2, aa2_2, aa3_2, aa4_2, vv_1, vv_2, bb1_1, bb2_1, bb3_1, bb4_1, bb1_2, bb2_2, bb3_2, bb4_2]
    linear_combination (1/4 : ℂ) * hd31 + (1/4 : ℂ) * hd32 + (-1/4 : ℂ) * hd33 + (-1/4 : ℂ) * hd34
  have fk13 : uu c 1 * star (uu c 3)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 1 3
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 1 3
        + vv d 1 * star (vv d 3) := by
    simp only [Trace5.fr, uu_1, uu_3, aa1_1, aa2_1, aa3_1, aa4_1, aa1_3, aa2_3, aa3_3, aa4_3, vv_1, vv_3, bb1_1, bb2_1, bb3_1, bb4_1, bb1_3, bb2_3, bb3_3, bb4_3]
    linear_combination (1/4 : ℂ) * hd11 + (1/4 : ℂ) * hd12 + (-1/4 : ℂ) * hd13 + (-1/4 : ℂ) * hd14
  have fk20 : uu c 2 * star (uu c 0)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 2 0
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 2 0
        + vv d 2 * star (vv d 0) := by
    simp only [Trace5.fr, uu_2, uu_0, aa1_2, aa2_2, aa3_2, aa4_2, aa1_0, aa2_0, aa3_0, aa4_0, vv_2, vv_0, bb1_2, bb2_2, bb3_2, bb4_2, bb1_0, bb2_0, bb3_0, bb4_0]
    linear_combination (1/4 : ℂ) * hd11 + (-1/4 : ℂ) * hd12 + (1/4 : ℂ) * hd13 + (-1/4 : ℂ) * hd14
  have fk21 : uu c 2 * star (uu c 1)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 2 1
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 2 1
        + vv d 2 * star (vv d 1) := by
    simp only [Trace5.fr, uu_2, uu_1, aa1_2, aa2_2, aa3_2, aa4_2, aa1_1, aa2_1, aa3_1, aa4_1, vv_2, vv_1, bb1_2, bb2_2, bb3_2, bb4_2, bb1_1, bb2_1, bb3_1, bb4_1]
    linear_combination (1/4 : ℂ) * hd31 + (-1/4 : ℂ) * hd32 + (1/4 : ℂ) * hd33 + (-1/4 : ℂ) * hd34
  have fk22 : uu c 2 * star (uu c 2)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 2 2
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 2 2
        + vv d 2 * star (vv d 2) := by
    simp only [Trace5.fr, uu_2, uu_2, aa1_2, aa2_2, aa3_2, aa4_2, aa1_2, aa2_2, aa3_2, aa4_2, vv_2, vv_2, bb1_2, bb2_2, bb3_2, bb4_2, bb1_2, bb2_2, bb3_2, bb4_2]
    have hc : ((Complex.normSq (c y2) + Complex.normSq (c y6) + Complex.normSq (c y10)
        + Complex.normSq (c y14) + Complex.normSq (c y18)
        : Real) : ℂ) = ((Complex.normSq (d z2) + Complex.normSq (d z6) + Complex.normSq (d z10)
        + Complex.normSq (d z14) + Complex.normSq (d z18) : Real) : ℂ) := by
      exact_mod_cast mg2
    push_cast [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have fk23 : uu c 2 * star (uu c 3)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 2 3
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 2 3
        + vv d 2 * star (vv d 3) := by
    simp only [Trace5.fr, uu_2, uu_3, aa1_2, aa2_2, aa3_2, aa4_2, aa1_3, aa2_3, aa3_3, aa4_3, vv_2, vv_3, bb1_2, bb2_2, bb3_2, bb4_2, bb1_3, bb2_3, bb3_3, bb4_3]
    linear_combination (1/4 : ℂ) * hd21 + (-1/4 : ℂ) * hd22 + (1/4 : ℂ) * hd23 + (-1/4 : ℂ) * hd24
  have fk30 : uu c 3 * star (uu c 0)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 3 0
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 3 0
        + vv d 3 * star (vv d 0) := by
    simp only [Trace5.fr, uu_3, uu_0, aa1_3, aa2_3, aa3_3, aa4_3, aa1_0, aa2_0, aa3_0, aa4_0, vv_3, vv_0, bb1_3, bb2_3, bb3_3, bb4_3, bb1_0, bb2_0, bb3_0, bb4_0]
    linear_combination (1/4 : ℂ) * hd31 + (-1/4 : ℂ) * hd32 + (-1/4 : ℂ) * hd33 + (1/4 : ℂ) * hd34
  have fk31 : uu c 3 * star (uu c 1)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 3 1
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 3 1
        + vv d 3 * star (vv d 1) := by
    simp only [Trace5.fr, uu_3, uu_1, aa1_3, aa2_3, aa3_3, aa4_3, aa1_1, aa2_1, aa3_1, aa4_1, vv_3, vv_1, bb1_3, bb2_3, bb3_3, bb4_3, bb1_1, bb2_1, bb3_1, bb4_1]
    linear_combination (1/4 : ℂ) * hd11 + (-1/4 : ℂ) * hd12 + (-1/4 : ℂ) * hd13 + (1/4 : ℂ) * hd14
  have fk32 : uu c 3 * star (uu c 2)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 3 2
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 3 2
        + vv d 3 * star (vv d 2) := by
    simp only [Trace5.fr, uu_3, uu_2, aa1_3, aa2_3, aa3_3, aa4_3, aa1_2, aa2_2, aa3_2, aa4_2, vv_3, vv_2, bb1_3, bb2_3, bb3_3, bb4_3, bb1_2, bb2_2, bb3_2, bb4_2]
    linear_combination (1/4 : ℂ) * hd21 + (-1/4 : ℂ) * hd22 + (-1/4 : ℂ) * hd23 + (1/4 : ℂ) * hd24
  have fk33 : uu c 3 * star (uu c 3)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) 3 3
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) 3 3
        + vv d 3 * star (vv d 3) := by
    simp only [Trace5.fr, uu_3, uu_3, aa1_3, aa2_3, aa3_3, aa4_3, aa1_3, aa2_3, aa3_3, aa4_3, vv_3, vv_3, bb1_3, bb2_3, bb3_3, bb4_3, bb1_3, bb2_3, bb3_3, bb4_3]
    have hc : ((Complex.normSq (c y3) + Complex.normSq (c y7) + Complex.normSq (c y11)
        + Complex.normSq (c y15) + Complex.normSq (c y19)
        : Real) : ℂ) = ((Complex.normSq (d z3) + Complex.normSq (d z7) + Complex.normSq (d z11)
        + Complex.normSq (d z15) + Complex.normSq (d z19) : Real) : ℂ) := by
      exact_mod_cast mg3
    push_cast [← SixQubit.star_mul_self] at hc
    linear_combination hc
  have hf : ∀ k l : Fin 4, uu c k * star (uu c l)
      + Trace5.fr (aa1 c) (aa2 c) (aa3 c) (aa4 c) k l
      = Trace5.fr (bb1 d) (bb2 d) (bb3 d) (bb4 d) k l + vv d k * star (vv d l) := by
    intro k l
    fin_cases k <;> fin_cases l
    exacts [fk00 , fk01 , fk02 , fk03 , fk10 , fk11 , fk12 , fk13 , fk20 , fk21 , fk22 , fk23 , fk30
      , fk31 , fk32 , fk33]
  have m100 : star (uu c 0) * bb1 d 0 + star (uu c 1) * bb1 d 1 + star (aa1 c 0) * vv d 0
      + star (aa1 c 1) * vv d 1 = 0 := by
    simp only [uu_0, uu_1, aa1_0, aa1_1, bb1_0, bb1_1, vv_0, vv_1]
    linear_combination (1/2 : ℂ) * ho1a + (1/2 : ℂ) * hz11
  have m101 : star (uu c 2) * bb1 d 0 + star (uu c 3) * bb1 d 1 + star (aa1 c 2) * vv d 0
      + star (aa1 c 3) * vv d 1 = 0 := by
    simp only [uu_2, uu_3, aa1_2, aa1_3, bb1_0, bb1_1, vv_0, vv_1]
    linear_combination (1/2 : ℂ) * hk10 + (1/2 : ℂ) * hk11
  have m110 : star (uu c 0) * bb1 d 2 + star (uu c 1) * bb1 d 3 + star (aa1 c 0) * vv d 2
      + star (aa1 c 1) * vv d 3 = 0 := by
    simp only [uu_0, uu_1, aa1_0, aa1_1, bb1_2, bb1_3, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * hk10 - (1/2 : ℂ) * hk11
  have m111 : star (uu c 2) * bb1 d 2 + star (uu c 3) * bb1 d 3 + star (aa1 c 2) * vv d 2
      + star (aa1 c 3) * vv d 3 = 0 := by
    simp only [uu_2, uu_3, aa1_2, aa1_3, bb1_2, bb1_3, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * ho1a - (1/2 : ℂ) * hz11
  have n100 : star (uu c 0) * bb1 d 0 + star (uu c 2) * bb1 d 2 + star (aa1 c 0) * vv d 0
      + star (aa1 c 2) * vv d 2 = 0 := by
    simp only [uu_0, uu_2, aa1_0, aa1_2, bb1_0, bb1_2, vv_0, vv_2]
    linear_combination (1/2 : ℂ) * ho1a + (1/2 : ℂ) * hz12
  have n101 : star (uu c 1) * bb1 d 0 + star (uu c 3) * bb1 d 2 + star (aa1 c 1) * vv d 0
      + star (aa1 c 3) * vv d 2 = 0 := by
    simp only [uu_1, uu_3, aa1_1, aa1_3, bb1_0, bb1_2, vv_0, vv_2]
    linear_combination (1/2 : ℂ) * hl10 + (1/2 : ℂ) * hl12
  have n110 : star (uu c 0) * bb1 d 1 + star (uu c 2) * bb1 d 3 + star (aa1 c 0) * vv d 1
      + star (aa1 c 2) * vv d 3 = 0 := by
    simp only [uu_0, uu_2, aa1_0, aa1_2, bb1_1, bb1_3, vv_1, vv_3]
    linear_combination (1/2 : ℂ) * hl10 - (1/2 : ℂ) * hl12
  have n111 : star (uu c 1) * bb1 d 1 + star (uu c 3) * bb1 d 3 + star (aa1 c 1) * vv d 1
      + star (aa1 c 3) * vv d 3 = 0 := by
    simp only [uu_1, uu_3, aa1_1, aa1_3, bb1_1, bb1_3, vv_1, vv_3]
    linear_combination (1/2 : ℂ) * ho1a - (1/2 : ℂ) * hz12
  have m200 : star (uu c 0) * bb2 d 0 + star (uu c 1) * bb2 d 1 + star (aa2 c 0) * vv d 0
      + star (aa2 c 1) * vv d 1 = 0 := by
    simp only [uu_0, uu_1, aa2_0, aa2_1, bb2_0, bb2_1, vv_0, vv_1]
    linear_combination (1/2 : ℂ) * ho2a + (1/2 : ℂ) * hz21
  have m201 : star (uu c 2) * bb2 d 0 + star (uu c 3) * bb2 d 1 + star (aa2 c 2) * vv d 0
      + star (aa2 c 3) * vv d 1 = 0 := by
    simp only [uu_2, uu_3, aa2_2, aa2_3, bb2_0, bb2_1, vv_0, vv_1]
    linear_combination (1/2 : ℂ) * hk20 + (1/2 : ℂ) * hk21
  have m210 : star (uu c 0) * bb2 d 2 + star (uu c 1) * bb2 d 3 + star (aa2 c 0) * vv d 2
      + star (aa2 c 1) * vv d 3 = 0 := by
    simp only [uu_0, uu_1, aa2_0, aa2_1, bb2_2, bb2_3, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * hk20 - (1/2 : ℂ) * hk21
  have m211 : star (uu c 2) * bb2 d 2 + star (uu c 3) * bb2 d 3 + star (aa2 c 2) * vv d 2
      + star (aa2 c 3) * vv d 3 = 0 := by
    simp only [uu_2, uu_3, aa2_2, aa2_3, bb2_2, bb2_3, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * ho2a - (1/2 : ℂ) * hz21
  have n200 : star (uu c 0) * bb2 d 0 + star (uu c 2) * bb2 d 2 + star (aa2 c 0) * vv d 0
      + star (aa2 c 2) * vv d 2 = 0 := by
    simp only [uu_0, uu_2, aa2_0, aa2_2, bb2_0, bb2_2, vv_0, vv_2]
    linear_combination (1/2 : ℂ) * ho2a + (1/2 : ℂ) * hz22
  have n201 : star (uu c 1) * bb2 d 0 + star (uu c 3) * bb2 d 2 + star (aa2 c 1) * vv d 0
      + star (aa2 c 3) * vv d 2 = 0 := by
    simp only [uu_1, uu_3, aa2_1, aa2_3, bb2_0, bb2_2, vv_0, vv_2]
    linear_combination (1/2 : ℂ) * hl20 + (1/2 : ℂ) * hl22
  have n210 : star (uu c 0) * bb2 d 1 + star (uu c 2) * bb2 d 3 + star (aa2 c 0) * vv d 1
      + star (aa2 c 2) * vv d 3 = 0 := by
    simp only [uu_0, uu_2, aa2_0, aa2_2, bb2_1, bb2_3, vv_1, vv_3]
    linear_combination (1/2 : ℂ) * hl20 - (1/2 : ℂ) * hl22
  have n211 : star (uu c 1) * bb2 d 1 + star (uu c 3) * bb2 d 3 + star (aa2 c 1) * vv d 1
      + star (aa2 c 3) * vv d 3 = 0 := by
    simp only [uu_1, uu_3, aa2_1, aa2_3, bb2_1, bb2_3, vv_1, vv_3]
    linear_combination (1/2 : ℂ) * ho2a - (1/2 : ℂ) * hz22
  have m300 : star (uu c 0) * bb3 d 0 + star (uu c 1) * bb3 d 1 + star (aa3 c 0) * vv d 0
      + star (aa3 c 1) * vv d 1 = 0 := by
    simp only [uu_0, uu_1, aa3_0, aa3_1, bb3_0, bb3_1, vv_0, vv_1]
    linear_combination (1/2 : ℂ) * ho3a + (1/2 : ℂ) * hz31
  have m301 : star (uu c 2) * bb3 d 0 + star (uu c 3) * bb3 d 1 + star (aa3 c 2) * vv d 0
      + star (aa3 c 3) * vv d 1 = 0 := by
    simp only [uu_2, uu_3, aa3_2, aa3_3, bb3_0, bb3_1, vv_0, vv_1]
    linear_combination (1/2 : ℂ) * hk30 + (1/2 : ℂ) * hk31
  have m310 : star (uu c 0) * bb3 d 2 + star (uu c 1) * bb3 d 3 + star (aa3 c 0) * vv d 2
      + star (aa3 c 1) * vv d 3 = 0 := by
    simp only [uu_0, uu_1, aa3_0, aa3_1, bb3_2, bb3_3, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * hk30 - (1/2 : ℂ) * hk31
  have m311 : star (uu c 2) * bb3 d 2 + star (uu c 3) * bb3 d 3 + star (aa3 c 2) * vv d 2
      + star (aa3 c 3) * vv d 3 = 0 := by
    simp only [uu_2, uu_3, aa3_2, aa3_3, bb3_2, bb3_3, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * ho3a - (1/2 : ℂ) * hz31
  have n300 : star (uu c 0) * bb3 d 0 + star (uu c 2) * bb3 d 2 + star (aa3 c 0) * vv d 0
      + star (aa3 c 2) * vv d 2 = 0 := by
    simp only [uu_0, uu_2, aa3_0, aa3_2, bb3_0, bb3_2, vv_0, vv_2]
    linear_combination (1/2 : ℂ) * ho3a + (1/2 : ℂ) * hz32
  have n301 : star (uu c 1) * bb3 d 0 + star (uu c 3) * bb3 d 2 + star (aa3 c 1) * vv d 0
      + star (aa3 c 3) * vv d 2 = 0 := by
    simp only [uu_1, uu_3, aa3_1, aa3_3, bb3_0, bb3_2, vv_0, vv_2]
    linear_combination (1/2 : ℂ) * hl30 + (1/2 : ℂ) * hl32
  have n310 : star (uu c 0) * bb3 d 1 + star (uu c 2) * bb3 d 3 + star (aa3 c 0) * vv d 1
      + star (aa3 c 2) * vv d 3 = 0 := by
    simp only [uu_0, uu_2, aa3_0, aa3_2, bb3_1, bb3_3, vv_1, vv_3]
    linear_combination (1/2 : ℂ) * hl30 - (1/2 : ℂ) * hl32
  have n311 : star (uu c 1) * bb3 d 1 + star (uu c 3) * bb3 d 3 + star (aa3 c 1) * vv d 1
      + star (aa3 c 3) * vv d 3 = 0 := by
    simp only [uu_1, uu_3, aa3_1, aa3_3, bb3_1, bb3_3, vv_1, vv_3]
    linear_combination (1/2 : ℂ) * ho3a - (1/2 : ℂ) * hz32
  have m400 : star (uu c 0) * bb4 d 0 + star (uu c 1) * bb4 d 1 + star (aa4 c 0) * vv d 0
      + star (aa4 c 1) * vv d 1 = 0 := by
    simp only [uu_0, uu_1, aa4_0, aa4_1, bb4_0, bb4_1, vv_0, vv_1]
    linear_combination (1/2 : ℂ) * ho4a + (1/2 : ℂ) * hz41
  have m401 : star (uu c 2) * bb4 d 0 + star (uu c 3) * bb4 d 1 + star (aa4 c 2) * vv d 0
      + star (aa4 c 3) * vv d 1 = 0 := by
    simp only [uu_2, uu_3, aa4_2, aa4_3, bb4_0, bb4_1, vv_0, vv_1]
    linear_combination (1/2 : ℂ) * hk40 + (1/2 : ℂ) * hk41
  have m410 : star (uu c 0) * bb4 d 2 + star (uu c 1) * bb4 d 3 + star (aa4 c 0) * vv d 2
      + star (aa4 c 1) * vv d 3 = 0 := by
    simp only [uu_0, uu_1, aa4_0, aa4_1, bb4_2, bb4_3, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * hk40 - (1/2 : ℂ) * hk41
  have m411 : star (uu c 2) * bb4 d 2 + star (uu c 3) * bb4 d 3 + star (aa4 c 2) * vv d 2
      + star (aa4 c 3) * vv d 3 = 0 := by
    simp only [uu_2, uu_3, aa4_2, aa4_3, bb4_2, bb4_3, vv_2, vv_3]
    linear_combination (1/2 : ℂ) * ho4a - (1/2 : ℂ) * hz41
  have n400 : star (uu c 0) * bb4 d 0 + star (uu c 2) * bb4 d 2 + star (aa4 c 0) * vv d 0
      + star (aa4 c 2) * vv d 2 = 0 := by
    simp only [uu_0, uu_2, aa4_0, aa4_2, bb4_0, bb4_2, vv_0, vv_2]
    linear_combination (1/2 : ℂ) * ho4a + (1/2 : ℂ) * hz42
  have n401 : star (uu c 1) * bb4 d 0 + star (uu c 3) * bb4 d 2 + star (aa4 c 1) * vv d 0
      + star (aa4 c 3) * vv d 2 = 0 := by
    simp only [uu_1, uu_3, aa4_1, aa4_3, bb4_0, bb4_2, vv_0, vv_2]
    linear_combination (1/2 : ℂ) * hl40 + (1/2 : ℂ) * hl42
  have n410 : star (uu c 0) * bb4 d 1 + star (uu c 2) * bb4 d 3 + star (aa4 c 0) * vv d 1
      + star (aa4 c 2) * vv d 3 = 0 := by
    simp only [uu_0, uu_2, aa4_0, aa4_2, bb4_1, bb4_3, vv_1, vv_3]
    linear_combination (1/2 : ℂ) * hl40 - (1/2 : ℂ) * hl42
  have n411 : star (uu c 1) * bb4 d 1 + star (uu c 3) * bb4 d 3 + star (aa4 c 1) * vv d 1
      + star (aa4 c 3) * vv d 3 = 0 := by
    simp only [uu_1, uu_3, aa4_1, aa4_3, bb4_1, bb4_3, vv_1, vv_3]
    linear_combination (1/2 : ℂ) * ho4a - (1/2 : ℂ) * hz42
  exact ⟨hnuu, hnvv, hnaa1, hnaa2, hnaa3, hnaa4, hnbb1, hnbb2, hnbb3, hnbb4, hq1, hq2, hq3, hq4, hf, x12, x13, x14, x23, x24, x34, m100, m101, m110, m111, n100, n101, n110, n111, m200, m201, m210, m211, n200, n201, n210, n211, m300, m301, m310, m311, n300, n301, n310, n311, m400, m401, m410, m411, n400, n401, n410, n411⟩

theorem physical_row_data (c d : SS.BitString 6 -> ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ y, y ∉ S1 → d y = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hdist : SS.HasDistance ![c, d] 3) : RowData c d :=
  row_data_of_rows c d
    (moments c d hc hd hnc hnd hdist)
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      f1 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      f1 f2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      f2 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      f2 f3 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      f3 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      f3 f4 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      f4 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      f4 f1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      f1 p1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      f1 p2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      k1 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      k1 p1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      l1 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      l1 p2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      f2 p1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      f2 p2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      k2 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      k2 p1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      l2 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      l2 p2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      f3 p1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      f3 p2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      k3 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      k3 p1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      l3 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      l3 p2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      f4 p1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      f4 p2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      k4 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      k4 p1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      l4 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      l4 p2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      g12 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      g13 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      g14 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      g23 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      g24 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hdist
      g34 w0 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      p1 w0 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      p1 w1 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      p1 w2 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      p1 w3 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      p2 w0 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      p2 w1 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      p2 w2 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      p2 w3 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      p3 w0 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      p3 w1 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      p3 w2 (by decide))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hdist
      p3 w3 (by decide))


end
end MainTheory.Orbit5PhysicalRowData
