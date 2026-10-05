import SixQubit.CodeOrbit35
import SixQubit.CodeOrbit37
import SixQubit.CodeOrbit38
import MainTheory.OrderEightSupportDisplays

/-! Literal SI order-five moment consequences of actual physical codewords.
Only normalization and degree-two diagonal moments are used. Every rational
constraint multiplier is checked by the Lean kernel, independently of all
phase exclusions and final no-code theorems. Zero amplitudes are allowed.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace MainTheory.OrderFivePrintedMoments
noncomputable section
open scoped BigOperators

namespace Orbit35
open SixQubit.Orbit35

theorem consequence0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q5 + r10 + r11 = (2/5) := by
  linear_combination (2/5) * hm.n1 + (2/5) * hm.m1 + (2/5) * hm.m2 + (2/5) * hm.m3 + (1/5) * hm.m4 + (1/5) * hm.m5 + (-3/5) * hm.m6 + (-3/5) * hm.c12 + (-3/5) * hm.c13 + (-1/5) * hm.c14 + (-1/5) * hm.c15 + (1/5) * hm.c16 + (2/5) * hm.c23 + (-1/5) * hm.c24 + (-1/5) * hm.c25 + (1/5) * hm.c26 + (-1/5) * hm.c34 + (-1/5) * hm.c35 + (1/5) * hm.c36 + (-2/5) * hm.c45 + (2/5) * hm.c46 + (2/5) * hm.c56

theorem consequence1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q7 - r10 = 0 := by
  linear_combination (-2/5) * hm.m4 + (-2/5) * hm.m5 + (4/5) * hm.m6 + (-2/5) * hm.c12 + (3/5) * hm.c13 + (1/5) * hm.c14 + (1/5) * hm.c15 + (-1/5) * hm.c16 + (-2/5) * hm.c23 + (1/5) * hm.c24 + (1/5) * hm.c25 + (-1/5) * hm.c26 + (1/5) * hm.c34 + (1/5) * hm.c35 + (-1/5) * hm.c36 + (2/5) * hm.c45 + (-2/5) * hm.c46 + (-2/5) * hm.c56

theorem consequence2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q8 - r11 = 0 := by
  linear_combination (-2/5) * hm.m4 + (-2/5) * hm.m5 + (4/5) * hm.m6 + (3/5) * hm.c12 + (-2/5) * hm.c13 + (1/5) * hm.c14 + (1/5) * hm.c15 + (-1/5) * hm.c16 + (-2/5) * hm.c23 + (1/5) * hm.c24 + (1/5) * hm.c25 + (-1/5) * hm.c26 + (1/5) * hm.c34 + (1/5) * hm.c35 + (-1/5) * hm.c36 + (2/5) * hm.c45 + (-2/5) * hm.c46 + (-2/5) * hm.c56

theorem consequence3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : r12 = (3/10) := by
  linear_combination (3/10) * hm.n1 + (3/10) * hm.m1 + (3/10) * hm.m2 + (3/10) * hm.m3 + (-3/10) * hm.m4 + (-3/10) * hm.m5 + (1/5) * hm.m6 + (-2/5) * hm.c12 + (-2/5) * hm.c13 + (1/5) * hm.c14 + (1/5) * hm.c15 + (-1/5) * hm.c16 + (-2/5) * hm.c23 + (1/5) * hm.c24 + (1/5) * hm.c25 + (-1/5) * hm.c26 + (1/5) * hm.c34 + (1/5) * hm.c35 + (-1/5) * hm.c36 + (-1/10) * hm.c45 + (1/10) * hm.c46 + (1/10) * hm.c56

theorem physical_consequences (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (Complex.normSq (c y5)) + (Complex.normSq (d z10)) + (Complex.normSq (d z11)) = (2/5) ∧
    (Complex.normSq (c y7)) - (Complex.normSq (d z10)) = 0 ∧
    (Complex.normSq (c y8)) - (Complex.normSq (d z11)) = 0 ∧
    (Complex.normSq (d z12)) = (3/10) := by
  have hm := SixQubit.Orbit35.moments c d hc hd hnc hnd hkl
  exact ⟨consequence0 hm,consequence1 hm,consequence2 hm,consequence3 hm⟩

end Orbit35

namespace Orbit37
open SixQubit.Orbit37

def A : Fin 3 → SS.BitString 6 := ![y2,y1,y0]
def B : Fin 3 → Fin 3 → SS.BitString 6 := ![![y3,y4,y5],![y6,y7,y8],![y9,y10,y11]]

theorem printed_labels :
    (∀ j, A j = MainTheory.OrderEightSupportDisplays.bits (![6,5,0] j)) ∧
    (∀ i j, B i j = MainTheory.OrderEightSupportDisplays.bits (![![25,26,31],![41,42,47],![49,50,55]] i j)) ∧
    y12 = MainTheory.OrderEightSupportDisplays.bits 60 := by
  decide +kernel

theorem consequence0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q12 = (1/10) := by
  linear_combination (1/10) * hm.n1 + (1/10) * hm.m1 + (1/10) * hm.m2 + (1/10) * hm.m3 + (-1/20) * hm.m4 + (1/20) * hm.m5 + (1/20) * hm.m6 + (1/4) * hm.c12 + (1/4) * hm.c13 + (1/2) * hm.c14 + (-1/2) * hm.c15 + (-1/2) * hm.c16 + (-1/4) * hm.c23

theorem consequence1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q3 + q4 + q5 = (1/5) := by
  linear_combination (1/5) * hm.n1 + (1/5) * hm.m1 + (1/5) * hm.m2 + (1/5) * hm.m3 + (-1/10) * hm.m4 + (1/10) * hm.m5 + (1/10) * hm.m6 + (-1/2) * hm.c12 + (-1/2) * hm.c13 + (1/2) * hm.c23

theorem consequence2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q6 + q7 + q8 = (1/5) := by
  linear_combination (1/5) * hm.n1 + (1/5) * hm.m1 + (1/5) * hm.m2 + (1/5) * hm.m3 + (-1/10) * hm.m4 + (1/10) * hm.m5 + (1/10) * hm.m6 + (-1/2) * hm.c12 + (1/2) * hm.c13 + (-1/2) * hm.c23

theorem consequence3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q10 + q11 + q9 = (1/5) := by
  linear_combination (1/5) * hm.n1 + (1/5) * hm.m1 + (1/5) * hm.m2 + (1/5) * hm.m3 + (-1/10) * hm.m4 + (1/10) * hm.m5 + (1/10) * hm.m6 + (1/2) * hm.c12 + (-1/2) * hm.c13 + (-1/2) * hm.c23

theorem consequence4 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q2 - q3 - q6 - q9 = (-1/10) := by
  linear_combination (-1/10) * hm.n1 + (-1/10) * hm.m1 + (-1/10) * hm.m2 + (-1/10) * hm.m3 + (-9/20) * hm.m4 + (29/20) * hm.m5 + (-31/20) * hm.m6 + (1/4) * hm.c12 + (1/4) * hm.c13 + (-1/2) * hm.c14 + (-1/2) * hm.c15 + (1/2) * hm.c16 + (3/4) * hm.c23 + -1 * hm.c25 + -1 * hm.c35 + 2 * hm.c46

theorem consequence5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q1 - q10 - q4 - q7 = (-1/10) := by
  linear_combination (-1/10) * hm.n1 + (-1/10) * hm.m1 + (-1/10) * hm.m2 + (-1/10) * hm.m3 + (-9/20) * hm.m4 + (-31/20) * hm.m5 + (29/20) * hm.m6 + (5/4) * hm.c12 + (5/4) * hm.c13 + (3/2) * hm.c14 + (-3/2) * hm.c15 + (-5/2) * hm.c16 + (-5/4) * hm.c23 + -1 * hm.c24 + 1 * hm.c25 + -1 * hm.c34 + 1 * hm.c35 + 2 * hm.c45

theorem consequence6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q0 - q11 - q5 - q8 = (-1/10) := by
  linear_combination 1 * hm.n0 + (-11/10) * hm.n1 + (-11/10) * hm.m1 + (-11/10) * hm.m2 + (-11/10) * hm.m3 + (31/20) * hm.m4 + (-11/20) * hm.m5 + (-11/20) * hm.m6 + (-3/4) * hm.c12 + (-3/4) * hm.c13 + (-3/2) * hm.c14 + (5/2) * hm.c15 + (5/2) * hm.c16 + (7/4) * hm.c23 + 1 * hm.c24 + 1 * hm.c34 + -2 * hm.c45 + -2 * hm.c46

theorem consequence7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q0 + q1 + q2 = (3/10) := by
  linear_combination 1 * hm.n0 + (-7/10) * hm.n1 + (-7/10) * hm.m1 + (-7/10) * hm.m2 + (-7/10) * hm.m3 + (7/20) * hm.m4 + (-7/20) * hm.m5 + (-7/20) * hm.m6 + (1/4) * hm.c12 + (1/4) * hm.c13 + (-1/2) * hm.c14 + (1/2) * hm.c15 + (1/2) * hm.c16 + (3/4) * hm.c23

theorem consequence8 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q0 - r12 = 0 := by
  linear_combination 1 * hm.n0 + -1 * hm.n1 + -1 * hm.m1 + -1 * hm.m2 + -1 * hm.m3 + (1/2) * hm.m4 + (-1/2) * hm.m5 + (-1/2) * hm.m6 + (-1/2) * hm.c12 + (-1/2) * hm.c13 + -1 * hm.c14 + 2 * hm.c15 + 2 * hm.c16 + (3/2) * hm.c23 + 1 * hm.c24 + 1 * hm.c34 + -1 * hm.c45 + -1 * hm.c46

theorem consequence9 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q1 - r11 = 0 := by
  linear_combination -1 * hm.m5 + 1 * hm.m6 + 1 * hm.c12 + 1 * hm.c13 + 1 * hm.c14 + -1 * hm.c15 + -2 * hm.c16 + -1 * hm.c23 + -1 * hm.c24 + 1 * hm.c25 + -1 * hm.c34 + 1 * hm.c35 + 1 * hm.c45

theorem consequence10 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q2 - r10 = 0 := by
  linear_combination 1 * hm.m5 + -1 * hm.m6 + -1 * hm.c14 + 1 * hm.c16 + 1 * hm.c23 + -1 * hm.c25 + -1 * hm.c35 + 1 * hm.c46

theorem consequence11 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q3 - r9 = 0 := by
  linear_combination (1/2) * hm.m4 + (-1/2) * hm.m5 + (1/2) * hm.m6 + (-1/2) * hm.c12 + (-1/2) * hm.c13 + 1 * hm.c15 + (1/2) * hm.c23 + -1 * hm.c46

theorem consequence12 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q4 - r8 = 0 := by
  linear_combination (1/2) * hm.m4 + (1/2) * hm.m5 + (-1/2) * hm.m6 + (-1/2) * hm.c12 + (-1/2) * hm.c13 + 1 * hm.c16 + (1/2) * hm.c23 + -1 * hm.c45

theorem consequence13 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q5 - r7 = 0 := by
  linear_combination 1 * hm.m1 + -1 * hm.m4 + -1 * hm.c15 + -1 * hm.c16 + 1 * hm.c45 + 1 * hm.c46

theorem consequence14 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q6 - r6 = 0 := by
  linear_combination (1/2) * hm.m4 + (-1/2) * hm.m5 + (1/2) * hm.m6 + (-1/2) * hm.c12 + (1/2) * hm.c13 + (-1/2) * hm.c23 + 1 * hm.c25 + -1 * hm.c46

theorem consequence15 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q7 - r5 = 0 := by
  linear_combination (1/2) * hm.m4 + (1/2) * hm.m5 + (-1/2) * hm.m6 + (-1/2) * hm.c12 + (-1/2) * hm.c13 + -1 * hm.c14 + 1 * hm.c15 + 1 * hm.c16 + (1/2) * hm.c23 + 1 * hm.c24 + -1 * hm.c25 + -1 * hm.c45

theorem consequence16 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q8 - r4 = 0 := by
  linear_combination 1 * hm.m2 + -1 * hm.m4 + 1 * hm.c13 + 1 * hm.c14 + -1 * hm.c15 + -1 * hm.c16 + -1 * hm.c23 + -1 * hm.c24 + 1 * hm.c45 + 1 * hm.c46

theorem consequence17 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q9 - r3 = 0 := by
  linear_combination (1/2) * hm.m4 + (-1/2) * hm.m5 + (1/2) * hm.m6 + (1/2) * hm.c12 + (-1/2) * hm.c13 + (-1/2) * hm.c23 + 1 * hm.c35 + -1 * hm.c46

theorem consequence18 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q10 - r2 = 0 := by
  linear_combination (1/2) * hm.m4 + (1/2) * hm.m5 + (-1/2) * hm.m6 + (-1/2) * hm.c12 + (-1/2) * hm.c13 + -1 * hm.c14 + 1 * hm.c15 + 1 * hm.c16 + (1/2) * hm.c23 + 1 * hm.c34 + -1 * hm.c35 + -1 * hm.c45

theorem consequence19 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q11 - r1 = 0 := by
  linear_combination 1 * hm.m3 + -1 * hm.m4 + 1 * hm.c12 + 1 * hm.c14 + -1 * hm.c15 + -1 * hm.c16 + -1 * hm.c23 + -1 * hm.c34 + 1 * hm.c45 + 1 * hm.c46

theorem consequence20 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q12 - r0 = 0 := by
  linear_combination (-1/2) * hm.m4 + (1/2) * hm.m5 + (1/2) * hm.m6 + (1/2) * hm.c12 + (1/2) * hm.c13 + 1 * hm.c14 + -1 * hm.c15 + -1 * hm.c16 + (-1/2) * hm.c23

theorem reconstruct {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hnq0 : 0 ≤ q0)
    (hnq1 : 0 ≤ q1)
    (hnq2 : 0 ≤ q2)
    (hnq3 : 0 ≤ q3)
    (hnq4 : 0 ≤ q4)
    (hnq5 : 0 ≤ q5)
    (hnq6 : 0 ≤ q6)
    (hnq7 : 0 ≤ q7)
    (hnq8 : 0 ≤ q8)
    (hnq9 : 0 ≤ q9)
    (hnq10 : 0 ≤ q10)
    (hnq11 : 0 ≤ q11)
    (hnq12 : 0 ≤ q12)
    (hnr0 : 0 ≤ r0)
    (hnr1 : 0 ≤ r1)
    (hnr2 : 0 ≤ r2)
    (hnr3 : 0 ≤ r3)
    (hnr4 : 0 ≤ r4)
    (hnr5 : 0 ≤ r5)
    (hnr6 : 0 ≤ r6)
    (hnr7 : 0 ≤ r7)
    (hnr8 : 0 ≤ r8)
    (hnr9 : 0 ≤ r9)
    (hnr10 : 0 ≤ r10)
    (hnr11 : 0 ≤ r11)
    (hnr12 : 0 ≤ r12)
    (h0 : q12 = (1/10))
    (h1 : q3 + q4 + q5 = (1/5))
    (h2 : q6 + q7 + q8 = (1/5))
    (h3 : q10 + q11 + q9 = (1/5))
    (h4 : q2 - q3 - q6 - q9 = (-1/10))
    (h5 : q1 - q10 - q4 - q7 = (-1/10))
    (h6 : q0 - q11 - q5 - q8 = (-1/10))
    (h8 : q0 - r12 = 0)
    (h9 : q1 - r11 = 0)
    (h10 : q2 - r10 = 0)
    (h11 : q3 - r9 = 0)
    (h12 : q4 - r8 = 0)
    (h13 : q5 - r7 = 0)
    (h14 : q6 - r6 = 0)
    (h15 : q7 - r5 = 0)
    (h16 : q8 - r4 = 0)
    (h17 : q9 - r3 = 0)
    (h18 : q10 - r2 = 0)
    (h19 : q11 - r1 = 0)
    (h20 : q12 - r0 = 0) : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 := by
  constructor <;> linarith only [hnq0,hnq1,hnq2,hnq3,hnq4,hnq5,hnq6,hnq7,hnq8,hnq9,hnq10,hnq11,hnq12,hnr0,hnr1,hnr2,hnr3,hnr4,hnr5,hnr6,hnr7,hnr8,hnr9,hnr10,hnr11,hnr12,h0,h1,h2,h3,h4,h5,h6,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20]

theorem physical_consequences (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (Complex.normSq (c y12)) = (1/10) ∧
    (Complex.normSq (c y3)) + (Complex.normSq (c y4)) + (Complex.normSq (c y5)) = (1/5) ∧
    (Complex.normSq (c y6)) + (Complex.normSq (c y7)) + (Complex.normSq (c y8)) = (1/5) ∧
    (Complex.normSq (c y10)) + (Complex.normSq (c y11)) + (Complex.normSq (c y9)) = (1/5) ∧
    (Complex.normSq (c y2)) - (Complex.normSq (c y3)) - (Complex.normSq (c y6)) - (Complex.normSq (c y9)) = (-1/10) ∧
    (Complex.normSq (c y1)) - (Complex.normSq (c y10)) - (Complex.normSq (c y4)) - (Complex.normSq (c y7)) = (-1/10) ∧
    (Complex.normSq (c y0)) - (Complex.normSq (c y11)) - (Complex.normSq (c y5)) - (Complex.normSq (c y8)) = (-1/10) ∧
    (Complex.normSq (c y0)) + (Complex.normSq (c y1)) + (Complex.normSq (c y2)) = (3/10) ∧
    (Complex.normSq (c y0)) - (Complex.normSq (d z12)) = 0 ∧
    (Complex.normSq (c y1)) - (Complex.normSq (d z11)) = 0 ∧
    (Complex.normSq (c y2)) - (Complex.normSq (d z10)) = 0 ∧
    (Complex.normSq (c y3)) - (Complex.normSq (d z9)) = 0 ∧
    (Complex.normSq (c y4)) - (Complex.normSq (d z8)) = 0 ∧
    (Complex.normSq (c y5)) - (Complex.normSq (d z7)) = 0 ∧
    (Complex.normSq (c y6)) - (Complex.normSq (d z6)) = 0 ∧
    (Complex.normSq (c y7)) - (Complex.normSq (d z5)) = 0 ∧
    (Complex.normSq (c y8)) - (Complex.normSq (d z4)) = 0 ∧
    (Complex.normSq (c y9)) - (Complex.normSq (d z3)) = 0 ∧
    (Complex.normSq (c y10)) - (Complex.normSq (d z2)) = 0 ∧
    (Complex.normSq (c y11)) - (Complex.normSq (d z1)) = 0 ∧
    (Complex.normSq (c y12)) - (Complex.normSq (d z0)) = 0 := by
  have hm := SixQubit.Orbit37.moments c d hc hd hnc hnd hkl
  exact ⟨consequence0 hm,consequence1 hm,consequence2 hm,consequence3 hm,consequence4 hm,consequence5 hm,consequence6 hm,consequence7 hm,consequence8 hm,consequence9 hm,consequence10 hm,consequence11 hm,consequence12 hm,consequence13 hm,consequence14 hm,consequence15 hm,consequence16 hm,consequence17 hm,consequence18 hm,consequence19 hm,consequence20 hm⟩

theorem physical_display (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Complex.normSq (c y12) = 1/10 ∧
    (∀ i : Fin 3, ∑ j : Fin 3, Complex.normSq (c (B i j)) = 1/5) ∧
    (∀ j : Fin 3, Complex.normSq (c (A j)) =
      (∑ i : Fin 3, Complex.normSq (c (B i j)))-1/10) := by
  have hm := SixQubit.Orbit37.moments c d hc hd hnc hnd hkl
  refine ⟨consequence0 hm,?_,?_⟩
  · intro i
    fin_cases i <;> norm_num [B,Fin.sum_univ_succ,Fin.succ] <;>
      linarith only [consequence1 hm,consequence2 hm,consequence3 hm]
  · intro j
    fin_cases j <;> norm_num [A,B,Fin.sum_univ_succ,Fin.succ] <;>
      linarith only [consequence4 hm,consequence5 hm,consequence6 hm]

end Orbit37

namespace Orbit38
open SixQubit.Orbit38

def A : Fin 4 → SS.BitString 6 := ![y3,y2,y1,y0]
def B : Fin 2 → Fin 4 → SS.BitString 6 := ![![y4,y5,y6,y7],![y8,y9,y10,y11]]

theorem printed_labels :
    (∀ j, A j = MainTheory.OrderEightSupportDisplays.bits (![9,5,3,0] j)) ∧
    (∀ i j, B i j = MainTheory.OrderEightSupportDisplays.bits (![![22,26,28,31],![38,42,44,47]] i j)) ∧
    y12 = MainTheory.OrderEightSupportDisplays.bits 49 := by
  decide +kernel

theorem consequence0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q12 = (1/5) := by
  linear_combination (1/5) * hm.n1 + (1/5) * hm.m1 + (1/5) * hm.m2 + (1/15) * hm.m3 + (1/15) * hm.m4 + (1/15) * hm.m5 + (-1/15) * hm.m6 + (1/3) * hm.c12 + (-1/6) * hm.c13 + (-1/6) * hm.c14 + (-1/6) * hm.c15 + (1/6) * hm.c16 + (-1/6) * hm.c23 + (-1/6) * hm.c24 + (-1/6) * hm.c25 + (1/6) * hm.c26

theorem consequence1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q4 + q5 + q6 + q7 = (3/10) := by
  linear_combination (3/10) * hm.n1 + (3/10) * hm.m1 + (3/10) * hm.m2 + (1/10) * hm.m3 + (1/10) * hm.m4 + (1/10) * hm.m5 + (-1/10) * hm.m6 + (-1/2) * hm.c12 + (-1/4) * hm.c13 + (-1/4) * hm.c14 + (-1/4) * hm.c15 + (1/4) * hm.c16 + (1/4) * hm.c23 + (1/4) * hm.c24 + (1/4) * hm.c25 + (-1/4) * hm.c26

theorem consequence2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q10 + q11 + q8 + q9 = (3/10) := by
  linear_combination (3/10) * hm.n1 + (3/10) * hm.m1 + (3/10) * hm.m2 + (1/10) * hm.m3 + (1/10) * hm.m4 + (1/10) * hm.m5 + (-1/10) * hm.m6 + (-1/2) * hm.c12 + (1/4) * hm.c13 + (1/4) * hm.c14 + (1/4) * hm.c15 + (-1/4) * hm.c16 + (-1/4) * hm.c23 + (-1/4) * hm.c24 + (-1/4) * hm.c25 + (1/4) * hm.c26

theorem consequence3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q3 - q4 - q8 = (-1/10) := by
  linear_combination (-1/10) * hm.n1 + (-1/10) * hm.m1 + (-1/10) * hm.m2 + (19/30) * hm.m3 + (-13/15) * hm.m4 + (-13/15) * hm.m5 + (13/15) * hm.m6 + (1/6) * hm.c12 + (-7/12) * hm.c13 + (5/12) * hm.c14 + (5/12) * hm.c15 + (-5/12) * hm.c16 + (-7/12) * hm.c23 + (5/12) * hm.c24 + (5/12) * hm.c25 + (-5/12) * hm.c26 + (1/2) * hm.c34 + (1/2) * hm.c35 + (-1/2) * hm.c36

theorem consequence4 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q2 - q5 - q9 = (-1/10) := by
  linear_combination (-1/10) * hm.n1 + (-1/10) * hm.m1 + (-1/10) * hm.m2 + (-7/10) * hm.m3 + (4/5) * hm.m4 + (-1/5) * hm.m5 + (1/5) * hm.m6 + (1/2) * hm.c12 + (1/4) * hm.c13 + (-3/4) * hm.c14 + (1/4) * hm.c15 + (-1/4) * hm.c16 + (1/4) * hm.c23 + (-3/4) * hm.c24 + (1/4) * hm.c25 + (-1/4) * hm.c26 + (1/2) * hm.c34 + (-1/2) * hm.c35 + (1/2) * hm.c36

theorem consequence5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q1 - q10 - q6 = (-1/10) := by
  linear_combination (-1/10) * hm.n1 + (-1/10) * hm.m1 + (-1/10) * hm.m2 + (-7/10) * hm.m3 + (-1/5) * hm.m4 + (4/5) * hm.m5 + (1/5) * hm.m6 + (1/2) * hm.c12 + (1/4) * hm.c13 + (1/4) * hm.c14 + (-3/4) * hm.c15 + (-1/4) * hm.c16 + (1/4) * hm.c23 + (1/4) * hm.c24 + (-3/4) * hm.c25 + (-1/4) * hm.c26 + (-1/2) * hm.c34 + (1/2) * hm.c35 + (1/2) * hm.c36

theorem consequence6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q0 - q11 - q7 = (-1/10) := by
  linear_combination 1 * hm.n0 + (-11/10) * hm.n1 + (-11/10) * hm.m1 + (-11/10) * hm.m2 + (3/10) * hm.m3 + (-1/5) * hm.m4 + (-1/5) * hm.m5 + (-4/5) * hm.m6 + (1/2) * hm.c12 + (1/4) * hm.c13 + (1/4) * hm.c14 + (1/4) * hm.c15 + (3/4) * hm.c16 + (1/4) * hm.c23 + (1/4) * hm.c24 + (1/4) * hm.c25 + (3/4) * hm.c26 + (-1/2) * hm.c34 + (-1/2) * hm.c35 + (-1/2) * hm.c36

theorem consequence7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q0 - r12 = 0 := by
  linear_combination 1 * hm.n0 + -1 * hm.n1 + -1 * hm.m1 + -1 * hm.m2 + (-1/3) * hm.m3 + (-1/3) * hm.m4 + (-1/3) * hm.m5 + (-2/3) * hm.m6 + (1/3) * hm.c12 + (1/3) * hm.c13 + (1/3) * hm.c14 + (1/3) * hm.c15 + (2/3) * hm.c16 + (1/3) * hm.c23 + (1/3) * hm.c24 + (1/3) * hm.c25 + (2/3) * hm.c26

theorem consequence8 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q1 - r11 = 0 := by
  linear_combination (-1/3) * hm.m3 + (-1/3) * hm.m4 + (2/3) * hm.m5 + (1/3) * hm.m6 + (1/3) * hm.c12 + (1/3) * hm.c13 + (1/3) * hm.c14 + (-2/3) * hm.c15 + (-1/3) * hm.c16 + (1/3) * hm.c23 + (1/3) * hm.c24 + (-2/3) * hm.c25 + (-1/3) * hm.c26

theorem consequence9 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q2 - r10 = 0 := by
  linear_combination (-1/3) * hm.m3 + (2/3) * hm.m4 + (-1/3) * hm.m5 + (1/3) * hm.m6 + (1/3) * hm.c12 + (1/3) * hm.c13 + (-2/3) * hm.c14 + (1/3) * hm.c15 + (-1/3) * hm.c16 + (1/3) * hm.c23 + (-2/3) * hm.c24 + (1/3) * hm.c25 + (-1/3) * hm.c26

theorem consequence10 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q3 - r9 = 0 := by
  linear_combination (2/3) * hm.m3 + (-1/3) * hm.m4 + (-1/3) * hm.m5 + (1/3) * hm.m6 + (1/3) * hm.c12 + (-2/3) * hm.c13 + (1/3) * hm.c14 + (1/3) * hm.c15 + (-1/3) * hm.c16 + (-2/3) * hm.c23 + (1/3) * hm.c24 + (1/3) * hm.c25 + (-1/3) * hm.c26

theorem consequence11 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q4 - r8 = 0 := by
  linear_combination (1/2) * hm.m4 + (1/2) * hm.m5 + (-1/2) * hm.m6 + (1/2) * hm.c13 + (-1/2) * hm.c14 + (-1/2) * hm.c15 + (1/2) * hm.c16 + (-1/2) * hm.c34 + (-1/2) * hm.c35 + (1/2) * hm.c36

theorem consequence12 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q5 - r7 = 0 := by
  linear_combination (1/3) * hm.m3 + (-1/6) * hm.m4 + (-1/6) * hm.m5 + (1/6) * hm.m6 + (-1/3) * hm.c12 + (-1/3) * hm.c13 + (2/3) * hm.c14 + (-1/3) * hm.c15 + (1/3) * hm.c16 + (1/6) * hm.c23 + (1/6) * hm.c24 + (1/6) * hm.c25 + (-1/6) * hm.c26 + (-1/2) * hm.c34 + (1/2) * hm.c35 + (-1/2) * hm.c36

theorem consequence13 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q6 - r6 = 0 := by
  linear_combination (1/3) * hm.m3 + (-1/6) * hm.m4 + (-1/6) * hm.m5 + (1/6) * hm.m6 + (-1/3) * hm.c12 + (-1/3) * hm.c13 + (-1/3) * hm.c14 + (2/3) * hm.c15 + (1/3) * hm.c16 + (1/6) * hm.c23 + (1/6) * hm.c24 + (1/6) * hm.c25 + (-1/6) * hm.c26 + (1/2) * hm.c34 + (-1/2) * hm.c35 + (-1/2) * hm.c36

theorem consequence14 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q7 - r5 = 0 := by
  linear_combination 1 * hm.m1 + (-2/3) * hm.m3 + (-1/6) * hm.m4 + (-1/6) * hm.m5 + (1/6) * hm.m6 + (-1/3) * hm.c12 + (-1/3) * hm.c13 + (-1/3) * hm.c14 + (-1/3) * hm.c15 + (-2/3) * hm.c16 + (1/6) * hm.c23 + (1/6) * hm.c24 + (1/6) * hm.c25 + (-1/6) * hm.c26 + (1/2) * hm.c34 + (1/2) * hm.c35 + (1/2) * hm.c36

theorem consequence15 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q8 - r4 = 0 := by
  linear_combination (1/2) * hm.m4 + (1/2) * hm.m5 + (-1/2) * hm.m6 + (1/2) * hm.c23 + (-1/2) * hm.c24 + (-1/2) * hm.c25 + (1/2) * hm.c26 + (-1/2) * hm.c34 + (-1/2) * hm.c35 + (1/2) * hm.c36

theorem consequence16 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q9 - r3 = 0 := by
  linear_combination (1/3) * hm.m3 + (-1/6) * hm.m4 + (-1/6) * hm.m5 + (1/6) * hm.m6 + (-1/3) * hm.c12 + (1/6) * hm.c13 + (1/6) * hm.c14 + (1/6) * hm.c15 + (-1/6) * hm.c16 + (-1/3) * hm.c23 + (2/3) * hm.c24 + (-1/3) * hm.c25 + (1/3) * hm.c26 + (-1/2) * hm.c34 + (1/2) * hm.c35 + (-1/2) * hm.c36

theorem consequence17 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q10 - r2 = 0 := by
  linear_combination (1/3) * hm.m3 + (-1/6) * hm.m4 + (-1/6) * hm.m5 + (1/6) * hm.m6 + (-1/3) * hm.c12 + (1/6) * hm.c13 + (1/6) * hm.c14 + (1/6) * hm.c15 + (-1/6) * hm.c16 + (-1/3) * hm.c23 + (-1/3) * hm.c24 + (2/3) * hm.c25 + (1/3) * hm.c26 + (1/2) * hm.c34 + (-1/2) * hm.c35 + (-1/2) * hm.c36

theorem consequence18 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q11 - r1 = 0 := by
  linear_combination 1 * hm.m2 + (-2/3) * hm.m3 + (-1/6) * hm.m4 + (-1/6) * hm.m5 + (1/6) * hm.m6 + (-1/3) * hm.c12 + (1/6) * hm.c13 + (1/6) * hm.c14 + (1/6) * hm.c15 + (-1/6) * hm.c16 + (-1/3) * hm.c23 + (-1/3) * hm.c24 + (-1/3) * hm.c25 + (-2/3) * hm.c26 + (1/2) * hm.c34 + (1/2) * hm.c35 + (1/2) * hm.c36

theorem consequence19 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) : q12 - r0 = 0 := by
  linear_combination (1/3) * hm.m3 + (1/3) * hm.m4 + (1/3) * hm.m5 + (-1/3) * hm.m6 + (2/3) * hm.c12 + (-1/3) * hm.c13 + (-1/3) * hm.c14 + (-1/3) * hm.c15 + (1/3) * hm.c16 + (-1/3) * hm.c23 + (-1/3) * hm.c24 + (-1/3) * hm.c25 + (1/3) * hm.c26

theorem reconstruct {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hnq0 : 0 ≤ q0)
    (hnq1 : 0 ≤ q1)
    (hnq2 : 0 ≤ q2)
    (hnq3 : 0 ≤ q3)
    (hnq4 : 0 ≤ q4)
    (hnq5 : 0 ≤ q5)
    (hnq6 : 0 ≤ q6)
    (hnq7 : 0 ≤ q7)
    (hnq8 : 0 ≤ q8)
    (hnq9 : 0 ≤ q9)
    (hnq10 : 0 ≤ q10)
    (hnq11 : 0 ≤ q11)
    (hnq12 : 0 ≤ q12)
    (hnr0 : 0 ≤ r0)
    (hnr1 : 0 ≤ r1)
    (hnr2 : 0 ≤ r2)
    (hnr3 : 0 ≤ r3)
    (hnr4 : 0 ≤ r4)
    (hnr5 : 0 ≤ r5)
    (hnr6 : 0 ≤ r6)
    (hnr7 : 0 ≤ r7)
    (hnr8 : 0 ≤ r8)
    (hnr9 : 0 ≤ r9)
    (hnr10 : 0 ≤ r10)
    (hnr11 : 0 ≤ r11)
    (hnr12 : 0 ≤ r12)
    (h0 : q12 = (1/5))
    (h1 : q4 + q5 + q6 + q7 = (3/10))
    (h2 : q10 + q11 + q8 + q9 = (3/10))
    (h3 : q3 - q4 - q8 = (-1/10))
    (h4 : q2 - q5 - q9 = (-1/10))
    (h5 : q1 - q10 - q6 = (-1/10))
    (h6 : q0 - q11 - q7 = (-1/10))
    (h7 : q0 - r12 = 0)
    (h8 : q1 - r11 = 0)
    (h9 : q2 - r10 = 0)
    (h10 : q3 - r9 = 0)
    (h11 : q4 - r8 = 0)
    (h12 : q5 - r7 = 0)
    (h13 : q6 - r6 = 0)
    (h14 : q7 - r5 = 0)
    (h15 : q8 - r4 = 0)
    (h16 : q9 - r3 = 0)
    (h17 : q10 - r2 = 0)
    (h18 : q11 - r1 = 0)
    (h19 : q12 - r0 = 0) : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 := by
  constructor <;> linarith only [hnq0,hnq1,hnq2,hnq3,hnq4,hnq5,hnq6,hnq7,hnq8,hnq9,hnq10,hnq11,hnq12,hnr0,hnr1,hnr2,hnr3,hnr4,hnr5,hnr6,hnr7,hnr8,hnr9,hnr10,hnr11,hnr12,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19]

theorem column_positive {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12) :
    (1/10 ≤ q4+q8 ∧ 0 < q4+q8) ∧
    (1/10 ≤ q5+q9 ∧ 0 < q5+q9) ∧
    (1/10 ≤ q6+q10 ∧ 0 < q6+q10) ∧
    (1/10 ≤ q7+q11 ∧ 0 < q7+q11) := by
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩,⟨?_,?_⟩⟩
  · linarith only [consequence3 hm,hm.nq3]
  · linarith only [consequence3 hm,hm.nq3]
  · linarith only [consequence4 hm,hm.nq2]
  · linarith only [consequence4 hm,hm.nq2]
  · linarith only [consequence5 hm,hm.nq1]
  · linarith only [consequence5 hm,hm.nq1]
  · linarith only [consequence6 hm,hm.nq0]
  · linarith only [consequence6 hm,hm.nq0]

theorem physical_consequences (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (Complex.normSq (c y12)) = (1/5) ∧
    (Complex.normSq (c y4)) + (Complex.normSq (c y5)) + (Complex.normSq (c y6)) + (Complex.normSq (c y7)) = (3/10) ∧
    (Complex.normSq (c y10)) + (Complex.normSq (c y11)) + (Complex.normSq (c y8)) + (Complex.normSq (c y9)) = (3/10) ∧
    (Complex.normSq (c y3)) - (Complex.normSq (c y4)) - (Complex.normSq (c y8)) = (-1/10) ∧
    (Complex.normSq (c y2)) - (Complex.normSq (c y5)) - (Complex.normSq (c y9)) = (-1/10) ∧
    (Complex.normSq (c y1)) - (Complex.normSq (c y10)) - (Complex.normSq (c y6)) = (-1/10) ∧
    (Complex.normSq (c y0)) - (Complex.normSq (c y11)) - (Complex.normSq (c y7)) = (-1/10) ∧
    (Complex.normSq (c y0)) - (Complex.normSq (d z12)) = 0 ∧
    (Complex.normSq (c y1)) - (Complex.normSq (d z11)) = 0 ∧
    (Complex.normSq (c y2)) - (Complex.normSq (d z10)) = 0 ∧
    (Complex.normSq (c y3)) - (Complex.normSq (d z9)) = 0 ∧
    (Complex.normSq (c y4)) - (Complex.normSq (d z8)) = 0 ∧
    (Complex.normSq (c y5)) - (Complex.normSq (d z7)) = 0 ∧
    (Complex.normSq (c y6)) - (Complex.normSq (d z6)) = 0 ∧
    (Complex.normSq (c y7)) - (Complex.normSq (d z5)) = 0 ∧
    (Complex.normSq (c y8)) - (Complex.normSq (d z4)) = 0 ∧
    (Complex.normSq (c y9)) - (Complex.normSq (d z3)) = 0 ∧
    (Complex.normSq (c y10)) - (Complex.normSq (d z2)) = 0 ∧
    (Complex.normSq (c y11)) - (Complex.normSq (d z1)) = 0 ∧
    (Complex.normSq (c y12)) - (Complex.normSq (d z0)) = 0 := by
  have hm := SixQubit.Orbit38.moments c d hc hd hnc hnd hkl
  exact ⟨consequence0 hm,consequence1 hm,consequence2 hm,consequence3 hm,consequence4 hm,consequence5 hm,consequence6 hm,consequence7 hm,consequence8 hm,consequence9 hm,consequence10 hm,consequence11 hm,consequence12 hm,consequence13 hm,consequence14 hm,consequence15 hm,consequence16 hm,consequence17 hm,consequence18 hm,consequence19 hm⟩

theorem physical_display (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Complex.normSq (c y12) = 1/5 ∧
    (∀ i : Fin 2, ∑ j : Fin 4, Complex.normSq (c (B i j)) = 3/10) ∧
    (∀ j : Fin 4, Complex.normSq (c (A j)) =
      (∑ i : Fin 2, Complex.normSq (c (B i j)))-1/10) := by
  have hm := SixQubit.Orbit38.moments c d hc hd hnc hnd hkl
  refine ⟨consequence0 hm,?_,?_⟩
  · intro i
    fin_cases i <;> norm_num [B,Fin.sum_univ_succ,Fin.succ] <;>
      linarith only [consequence1 hm,consequence2 hm]
  · intro j
    fin_cases j <;> norm_num [A,B,Fin.sum_univ_succ,Fin.succ] <;>
      linarith only [consequence3 hm,consequence4 hm,consequence5 hm,consequence6 hm]

theorem physical_column_positive (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x = 0) (hd : ∀ x, x ∉ S1 → d x = 0)
    (hnc : SS.innerC c c = 1) (hnd : SS.innerC d d = 1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∀ j : Fin 4, 1/10 ≤ Complex.normSq (c (B 0 j))+Complex.normSq (c (B 1 j)) ∧
      0 < Complex.normSq (c (B 0 j))+Complex.normSq (c (B 1 j)) := by
  have hm := SixQubit.Orbit38.moments c d hc hd hnc hnd hkl
  have hp := column_positive hm
  intro j
  fin_cases j <;> norm_num [B,Fin.succ] <;> tauto

end Orbit38

end
end MainTheory.OrderFivePrintedMoments
