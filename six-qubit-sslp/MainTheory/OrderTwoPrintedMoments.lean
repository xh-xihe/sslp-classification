import SixQubit.CodeOrbit42
import SixQubit.CodeOrbit43
import SixQubit.CodeOrbit44
import SixQubit.CodeOrbit46
import MainTheory.OrderEightSupportDisplays

/-! Both directions of the literal SI probability normal forms, over ℝ.
The rational row combinations are checked against the actual native moments.
The source words and both probability boundaries are retained explicitly.
No final no-code theorem is used to derive any normal form.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.OrderTwoPrintedMoments
noncomputable section

namespace Orbit42
open SixQubit.Orbit42
def bottom : Fin 10 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9]
def top : Fin 10 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9]
def bottomProb (a b g : ℝ) : Fin 10 → ℝ := ![1/4,1/4,-a - b - g + 1/4,-a - b - g + 1/4,a,a,b,b,g,g]
def topProb (a b g : ℝ) : Fin 10 → ℝ := ![1/4,1/4,-a - b - g + 1/4,-a - b - g + 1/4,a,a,b,b,g,g]
def Domain (a b g : ℝ) : Prop := 0≤(a) ∧ 0≤(b) ∧ 0≤(g) ∧ 0≤(-a - b - g + 1/4)
def Moment (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) := MomentSystem (p ⟨0,by decide⟩) (p ⟨1,by decide⟩) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨4,by decide⟩) (p ⟨5,by decide⟩) (p ⟨6,by decide⟩) (p ⟨7,by decide⟩) (p ⟨8,by decide⟩) (p ⟨9,by decide⟩) (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩)
theorem actual_words :
    (∀ i, bottom i=MainTheory.OrderEightSupportDisplays.bits (![0,3,29,30,45,46,53,54,57,58] i)) ∧
    (∀ i, top i=MainTheory.OrderEightSupportDisplays.bits (![1,2,28,31,44,47,52,55,56,59] i)) ∧
    S0=Finset.univ.image bottom ∧ S1=Finset.univ.image top := by decide +kernel

theorem consequence0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q0=1/4 := by
  linear_combination 1 * hm.n0 + (-3/4) * hm.n1 + (-1/4) * hm.m1 + (-1/4) * hm.m2 + (-1/4) * hm.m3 + (-1/4) * hm.m4 + (-3/4) * hm.m5 + (-3/4) * hm.m6 + (1/6) * hm.m15 + (1/6) * hm.m16 + (1/6) * hm.m25 + (1/6) * hm.m26 + (1/6) * hm.m35 + (1/6) * hm.m36 + (1/6) * hm.m45 + (1/6) * hm.m46 + (1/2) * hm.m56

theorem consequence1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q1=1/4 := by
  linear_combination (1/4) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/12) * hm.m4 + (1/4) * hm.m5 + (1/4) * hm.m6 + (-1/6) * hm.m15 + (-1/6) * hm.m16 + (-1/6) * hm.m25 + (-1/6) * hm.m26 + (-1/6) * hm.m35 + (-1/6) * hm.m36 + (-1/6) * hm.m45 + (-1/6) * hm.m46 + (1/2) * hm.m56

theorem consequence2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q2=-q4 - q6 - q8 + 1/4 := by
  linear_combination (1/4) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/12) * hm.m4 + (1/4) * hm.m5 + (1/4) * hm.m6 + (-1/6) * hm.m15 + (1/6) * hm.m16 + (-1/6) * hm.m25 + (1/6) * hm.m26 + (-1/6) * hm.m35 + (1/6) * hm.m36 + (-1/6) * hm.m45 + (1/6) * hm.m46 + (-1/2) * hm.m56

theorem consequence3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q3=-q4 - q6 - q8 + 1/4 := by
  linear_combination (1/4) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/12) * hm.m4 + (1/4) * hm.m5 + (1/4) * hm.m6 + (-5/6) * hm.m15 + (5/6) * hm.m16 + (1/6) * hm.m25 + (-1/6) * hm.m26 + (1/6) * hm.m35 + (-1/6) * hm.m36 + (1/6) * hm.m45 + (-1/6) * hm.m46 + (-1/2) * hm.m56

theorem consequence4 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q4=q4 := by
  ring

theorem consequence5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q5=q4 := by
  linear_combination (1/3) * hm.m15 + (-1/3) * hm.m16 + (-2/3) * hm.m25 + (2/3) * hm.m26 + (1/3) * hm.m35 + (-1/3) * hm.m36 + (1/3) * hm.m45 + (-1/3) * hm.m46

theorem consequence6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q6=q6 := by
  ring

theorem consequence7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q7=q6 := by
  linear_combination (1/3) * hm.m15 + (-1/3) * hm.m16 + (1/3) * hm.m25 + (-1/3) * hm.m26 + (-2/3) * hm.m35 + (2/3) * hm.m36 + (1/3) * hm.m45 + (-1/3) * hm.m46

theorem consequence8 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q8=q8 := by
  ring

theorem consequence9 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q9=q8 := by
  linear_combination (1/3) * hm.m15 + (-1/3) * hm.m16 + (1/3) * hm.m25 + (-1/3) * hm.m26 + (1/3) * hm.m35 + (-1/3) * hm.m36 + (-2/3) * hm.m45 + (2/3) * hm.m46

theorem consequence10 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r0=1/4 := by
  linear_combination (1/4) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/12) * hm.m4 + (1/4) * hm.m5 + (-3/4) * hm.m6 + (-1/6) * hm.m15 + (1/6) * hm.m16 + (-1/6) * hm.m25 + (1/6) * hm.m26 + (-1/6) * hm.m35 + (1/6) * hm.m36 + (-1/6) * hm.m45 + (1/6) * hm.m46 + (1/2) * hm.m56

theorem consequence11 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r1=1/4 := by
  linear_combination (1/4) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/12) * hm.m4 + (-3/4) * hm.m5 + (1/4) * hm.m6 + (1/6) * hm.m15 + (-1/6) * hm.m16 + (1/6) * hm.m25 + (-1/6) * hm.m26 + (1/6) * hm.m35 + (-1/6) * hm.m36 + (1/6) * hm.m45 + (-1/6) * hm.m46 + (1/2) * hm.m56

theorem consequence12 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r2=-q4 - q6 - q8 + 1/4 := by
  linear_combination (1/4) * hm.n1 + (3/4) * hm.m1 + (-1/4) * hm.m2 + (-1/4) * hm.m3 + (-1/4) * hm.m4 + (1/4) * hm.m5 + (1/4) * hm.m6 + (-5/6) * hm.m15 + (1/6) * hm.m16 + (1/6) * hm.m25 + (1/6) * hm.m26 + (1/6) * hm.m35 + (1/6) * hm.m36 + (1/6) * hm.m45 + (1/6) * hm.m46 + (-1/2) * hm.m56

theorem consequence13 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r3=-q4 - q6 - q8 + 1/4 := by
  linear_combination (1/4) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/12) * hm.m4 + (1/4) * hm.m5 + (1/4) * hm.m6 + (-1/6) * hm.m15 + (5/6) * hm.m16 + (-1/6) * hm.m25 + (-1/6) * hm.m26 + (-1/6) * hm.m35 + (-1/6) * hm.m36 + (-1/6) * hm.m45 + (-1/6) * hm.m46 + (-1/2) * hm.m56

theorem consequence14 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r4=q4 := by
  linear_combination (-1/3) * hm.m1 + (2/3) * hm.m2 + (-1/3) * hm.m3 + (-1/3) * hm.m4 + (1/3) * hm.m15 + (-2/3) * hm.m25 + (1/3) * hm.m35 + (1/3) * hm.m45

theorem consequence15 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r5=q4 := by
  linear_combination (-1/3) * hm.m16 + (2/3) * hm.m26 + (-1/3) * hm.m36 + (-1/3) * hm.m46

theorem consequence16 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r6=q6 := by
  linear_combination (-1/3) * hm.m1 + (-1/3) * hm.m2 + (2/3) * hm.m3 + (-1/3) * hm.m4 + (1/3) * hm.m15 + (1/3) * hm.m25 + (-2/3) * hm.m35 + (1/3) * hm.m45

theorem consequence17 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r7=q6 := by
  linear_combination (-1/3) * hm.m16 + (-1/3) * hm.m26 + (2/3) * hm.m36 + (-1/3) * hm.m46

theorem consequence18 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r8=q8 := by
  linear_combination (-1/3) * hm.m1 + (-1/3) * hm.m2 + (-1/3) * hm.m3 + (2/3) * hm.m4 + (1/3) * hm.m15 + (1/3) * hm.m25 + (1/3) * hm.m35 + (-2/3) * hm.m45

theorem consequence19 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r9=q8 := by
  linear_combination (-1/3) * hm.m16 + (-1/3) * hm.m26 + (-1/3) * hm.m36 + (2/3) * hm.m46

theorem normal_coordinates (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) (hm : Moment p q) :
    p=bottomProb (p ⟨4,by decide⟩) (p ⟨6,by decide⟩) (p ⟨8,by decide⟩) ∧ q=topProb (p ⟨4,by decide⟩) (p ⟨6,by decide⟩) (p ⟨8,by decide⟩) := by
  have h0 := consequence0 hm
  have h1 := consequence1 hm
  have h2 := consequence2 hm
  have h3 := consequence3 hm
  have h4 := consequence4 hm
  have h5 := consequence5 hm
  have h6 := consequence6 hm
  have h7 := consequence7 hm
  have h8 := consequence8 hm
  have h9 := consequence9 hm
  have h10 := consequence10 hm
  have h11 := consequence11 hm
  have h12 := consequence12 hm
  have h13 := consequence13 hm
  have h14 := consequence14 hm
  have h15 := consequence15 hm
  have h16 := consequence16 hm
  have h17 := consequence17 hm
  have h18 := consequence18 hm
  have h19 := consequence19 hm
  constructor
  · ext i
    fin_cases i <;> norm_num [bottomProb,Fin.succ] at * <;> linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19]
  · ext i
    fin_cases i <;> norm_num [topProb,Fin.succ] at * <;> linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19]

theorem domain_of_moment (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) (hm : Moment p q) : Domain (p ⟨4,by decide⟩) (p ⟨6,by decide⟩) (p ⟨8,by decide⟩) := by
  have h0 := consequence0 hm
  have h1 := consequence1 hm
  have h2 := consequence2 hm
  have h3 := consequence3 hm
  have h4 := consequence4 hm
  have h5 := consequence5 hm
  have h6 := consequence6 hm
  have h7 := consequence7 hm
  have h8 := consequence8 hm
  have h9 := consequence9 hm
  have h10 := consequence10 hm
  have h11 := consequence11 hm
  have h12 := consequence12 hm
  have h13 := consequence13 hm
  have h14 := consequence14 hm
  have h15 := consequence15 hm
  have h16 := consequence16 hm
  have h17 := consequence17 hm
  have h18 := consequence18 hm
  have h19 := consequence19 hm
  unfold Domain
  refine ⟨?_ ,?_ ,?_ ,?_⟩ <;>
    linarith only [hm.nq0,hm.nq1,hm.nq2,hm.nq3,hm.nq4,hm.nq5,hm.nq6,hm.nq7,hm.nq8,hm.nq9,hm.nr0,hm.nr1,hm.nr2,hm.nr3,hm.nr4,hm.nr5,hm.nr6,hm.nr7,hm.nr8,hm.nr9,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19]

theorem reconstruct (a b g : ℝ) (h : Domain a b g) :
    Moment (bottomProb a b g) (topProb a b g) := by
  obtain ⟨h0,h1,h2,h3⟩ := h
  change MomentSystem (bottomProb a b g ⟨0,by decide⟩) (bottomProb a b g ⟨1,by decide⟩) (bottomProb a b g ⟨2,by decide⟩) (bottomProb a b g ⟨3,by decide⟩) (bottomProb a b g ⟨4,by decide⟩) (bottomProb a b g ⟨5,by decide⟩) (bottomProb a b g ⟨6,by decide⟩) (bottomProb a b g ⟨7,by decide⟩) (bottomProb a b g ⟨8,by decide⟩) (bottomProb a b g ⟨9,by decide⟩) (topProb a b g ⟨0,by decide⟩) (topProb a b g ⟨1,by decide⟩) (topProb a b g ⟨2,by decide⟩) (topProb a b g ⟨3,by decide⟩) (topProb a b g ⟨4,by decide⟩) (topProb a b g ⟨5,by decide⟩) (topProb a b g ⟨6,by decide⟩) (topProb a b g ⟨7,by decide⟩) (topProb a b g ⟨8,by decide⟩) (topProb a b g ⟨9,by decide⟩)
  constructor <;> norm_num [bottomProb,topProb] <;> linarith only [h0,h1,h2,h3]

theorem complete_iff (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) :
    Moment p q ↔ ∃ a b g : ℝ, Domain a b g ∧ p=bottomProb a b g ∧ q=topProb a b g := by
  constructor
  · intro hm
    exact ⟨(p ⟨4,by decide⟩),(p ⟨6,by decide⟩),(p ⟨8,by decide⟩),domain_of_moment p q hm,normal_coordinates p q hm⟩
  · rintro ⟨a,b,g,hd,hp,hq⟩
    rw [hp,hq]
    exact reconstruct a b g hd

theorem actual_matched_flip : ∀ i,
    top i=SS.bxor (bottom i) (SS.stdBasis ⟨5,by decide⟩) := by decide +kernel

theorem matched_probabilities (p q : Fin 10 → ℝ) (hm : Moment p q) : p=q := by
  obtain ⟨hp,hq⟩ := normal_coordinates p q hm
  exact hp.trans hq.symm

theorem physical_normal_form (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∃ a b g : ℝ, Domain a b g ∧
      (fun i => Complex.normSq (c (bottom i)))=bottomProb a b g ∧
      (fun i => Complex.normSq (d (top i)))=topProb a b g := by
  apply (complete_iff _ _).1
  exact moments c d hc hd hnc hnd hkl
end Orbit42

namespace Orbit43
open SixQubit.Orbit43
def bottom : Fin 10 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9]
def top : Fin 10 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9]
def bottomProb (a b g : ℝ) : Fin 10 → ℝ := ![1/4,1/4,-a - b - g + 1/4,-a - b - g + 1/4,a,a,b,b,g,g]
def topProb (a b g : ℝ) : Fin 10 → ℝ := ![1/4,1/4,-a - b - g + 1/4,-a - b - g + 1/4,a,a,b,b,g,g]
def Domain (a b g : ℝ) : Prop := 0≤(a) ∧ 0≤(b) ∧ 0≤(g) ∧ 0≤(-a - b - g + 1/4)
def Moment (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) := MomentSystem (p ⟨0,by decide⟩) (p ⟨1,by decide⟩) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨4,by decide⟩) (p ⟨5,by decide⟩) (p ⟨6,by decide⟩) (p ⟨7,by decide⟩) (p ⟨8,by decide⟩) (p ⟨9,by decide⟩) (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩)
theorem actual_words :
    (∀ i, bottom i=MainTheory.OrderEightSupportDisplays.bits (![0,3,13,14,21,22,37,38,57,58] i)) ∧
    (∀ i, top i=MainTheory.OrderEightSupportDisplays.bits (![1,2,12,15,20,23,36,39,56,59] i)) ∧
    S0=Finset.univ.image bottom ∧ S1=Finset.univ.image top := by decide +kernel

theorem consequence0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q0=1/4 := by
  linear_combination 1 * hm.n0 + (-3/4) * hm.n1 + (-1/4) * hm.m1 + (-1/4) * hm.m2 + (-1/4) * hm.m3 + (-1/2) * hm.m4 + (-3/4) * hm.m5 + (-3/4) * hm.m6 + (1/6) * hm.m15 + (1/6) * hm.m16 + (1/6) * hm.m25 + (1/6) * hm.m26 + (1/6) * hm.m35 + (1/6) * hm.m36 + (1/3) * hm.m45 + (1/3) * hm.m46 + (1/2) * hm.m56

theorem consequence1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q1=1/4 := by
  linear_combination (1/4) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/6) * hm.m4 + (1/4) * hm.m5 + (1/4) * hm.m6 + (-1/6) * hm.m15 + (-1/6) * hm.m16 + (-1/6) * hm.m25 + (-1/6) * hm.m26 + (-1/6) * hm.m35 + (-1/6) * hm.m36 + (-1/3) * hm.m45 + (-1/3) * hm.m46 + (1/2) * hm.m56

theorem consequence2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q2=-q4 - q6 - q8 + 1/4 := by
  linear_combination (1/4) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/6) * hm.m4 + (1/4) * hm.m5 + (1/4) * hm.m6 + (-1/6) * hm.m15 + (1/6) * hm.m16 + (-1/6) * hm.m25 + (1/6) * hm.m26 + (-1/6) * hm.m35 + (1/6) * hm.m36 + (-1/3) * hm.m45 + (1/3) * hm.m46 + (-1/2) * hm.m56

theorem consequence3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q3=-q4 - q6 - q8 + 1/4 := by
  linear_combination (1/4) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/6) * hm.m4 + (1/4) * hm.m5 + (1/4) * hm.m6 + (-1/2) * hm.m15 + (1/2) * hm.m16 + (-1/2) * hm.m25 + (1/2) * hm.m26 + (1/2) * hm.m35 + (-1/2) * hm.m36 + (-1/2) * hm.m56

theorem consequence4 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q4=q4 := by
  ring

theorem consequence5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q5=q4 := by
  linear_combination (-1/3) * hm.m15 + (1/3) * hm.m16 + (2/3) * hm.m25 + (-2/3) * hm.m26 + (-1/3) * hm.m35 + (1/3) * hm.m36 + (1/3) * hm.m45 + (-1/3) * hm.m46

theorem consequence6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q6=q6 := by
  ring

theorem consequence7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q7=q6 := by
  linear_combination (2/3) * hm.m15 + (-2/3) * hm.m16 + (-1/3) * hm.m25 + (1/3) * hm.m26 + (-1/3) * hm.m35 + (1/3) * hm.m36 + (1/3) * hm.m45 + (-1/3) * hm.m46

theorem consequence8 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q8=q8 := by
  ring

theorem consequence9 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q9=q8 := by
  linear_combination (1/3) * hm.m15 + (-1/3) * hm.m16 + (1/3) * hm.m25 + (-1/3) * hm.m26 + (1/3) * hm.m35 + (-1/3) * hm.m36 + (-1/3) * hm.m45 + (1/3) * hm.m46

theorem consequence10 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r0=1/4 := by
  linear_combination (1/4) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/6) * hm.m4 + (1/4) * hm.m5 + (-3/4) * hm.m6 + (-1/6) * hm.m15 + (1/6) * hm.m16 + (-1/6) * hm.m25 + (1/6) * hm.m26 + (-1/6) * hm.m35 + (1/6) * hm.m36 + (-1/3) * hm.m45 + (1/3) * hm.m46 + (1/2) * hm.m56

theorem consequence11 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r1=1/4 := by
  linear_combination (1/4) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/6) * hm.m4 + (-3/4) * hm.m5 + (1/4) * hm.m6 + (1/6) * hm.m15 + (-1/6) * hm.m16 + (1/6) * hm.m25 + (-1/6) * hm.m26 + (1/6) * hm.m35 + (-1/6) * hm.m36 + (1/3) * hm.m45 + (-1/3) * hm.m46 + (1/2) * hm.m56

theorem consequence12 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r2=-q4 - q6 - q8 + 1/4 := by
  linear_combination (1/4) * hm.n1 + (5/12) * hm.m1 + (5/12) * hm.m2 + (-7/12) * hm.m3 + (-1/6) * hm.m4 + (1/4) * hm.m5 + (1/4) * hm.m6 + (-1/2) * hm.m15 + (1/6) * hm.m16 + (-1/2) * hm.m25 + (1/6) * hm.m26 + (1/2) * hm.m35 + (1/6) * hm.m36 + (1/3) * hm.m46 + (-1/2) * hm.m56

theorem consequence13 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r3=-q4 - q6 - q8 + 1/4 := by
  linear_combination (1/4) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/6) * hm.m4 + (1/4) * hm.m5 + (1/4) * hm.m6 + (-1/6) * hm.m15 + (1/2) * hm.m16 + (-1/6) * hm.m25 + (1/2) * hm.m26 + (-1/6) * hm.m35 + (-1/2) * hm.m36 + (-1/3) * hm.m45 + (-1/2) * hm.m56

theorem consequence14 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r4=q4 := by
  linear_combination (1/3) * hm.m1 + (-2/3) * hm.m2 + (1/3) * hm.m3 + (-1/3) * hm.m4 + (-1/3) * hm.m15 + (2/3) * hm.m25 + (-1/3) * hm.m35 + (1/3) * hm.m45

theorem consequence15 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r5=q4 := by
  linear_combination (1/3) * hm.m16 + (-2/3) * hm.m26 + (1/3) * hm.m36 + (-1/3) * hm.m46

theorem consequence16 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r6=q6 := by
  linear_combination (-2/3) * hm.m1 + (1/3) * hm.m2 + (1/3) * hm.m3 + (-1/3) * hm.m4 + (2/3) * hm.m15 + (-1/3) * hm.m25 + (-1/3) * hm.m35 + (1/3) * hm.m45

theorem consequence17 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r7=q6 := by
  linear_combination (-2/3) * hm.m16 + (1/3) * hm.m26 + (1/3) * hm.m36 + (-1/3) * hm.m46

theorem consequence18 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r8=q8 := by
  linear_combination (-1/3) * hm.m1 + (-1/3) * hm.m2 + (-1/3) * hm.m3 + (1/3) * hm.m4 + (1/3) * hm.m15 + (1/3) * hm.m25 + (1/3) * hm.m35 + (-1/3) * hm.m45

theorem consequence19 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r9=q8 := by
  linear_combination (-1/3) * hm.m16 + (-1/3) * hm.m26 + (-1/3) * hm.m36 + (1/3) * hm.m46

theorem normal_coordinates (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) (hm : Moment p q) :
    p=bottomProb (p ⟨4,by decide⟩) (p ⟨6,by decide⟩) (p ⟨8,by decide⟩) ∧ q=topProb (p ⟨4,by decide⟩) (p ⟨6,by decide⟩) (p ⟨8,by decide⟩) := by
  have h0 := consequence0 hm
  have h1 := consequence1 hm
  have h2 := consequence2 hm
  have h3 := consequence3 hm
  have h4 := consequence4 hm
  have h5 := consequence5 hm
  have h6 := consequence6 hm
  have h7 := consequence7 hm
  have h8 := consequence8 hm
  have h9 := consequence9 hm
  have h10 := consequence10 hm
  have h11 := consequence11 hm
  have h12 := consequence12 hm
  have h13 := consequence13 hm
  have h14 := consequence14 hm
  have h15 := consequence15 hm
  have h16 := consequence16 hm
  have h17 := consequence17 hm
  have h18 := consequence18 hm
  have h19 := consequence19 hm
  constructor
  · ext i
    fin_cases i <;> norm_num [bottomProb,Fin.succ] at * <;> linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19]
  · ext i
    fin_cases i <;> norm_num [topProb,Fin.succ] at * <;> linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19]

theorem domain_of_moment (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) (hm : Moment p q) : Domain (p ⟨4,by decide⟩) (p ⟨6,by decide⟩) (p ⟨8,by decide⟩) := by
  have h0 := consequence0 hm
  have h1 := consequence1 hm
  have h2 := consequence2 hm
  have h3 := consequence3 hm
  have h4 := consequence4 hm
  have h5 := consequence5 hm
  have h6 := consequence6 hm
  have h7 := consequence7 hm
  have h8 := consequence8 hm
  have h9 := consequence9 hm
  have h10 := consequence10 hm
  have h11 := consequence11 hm
  have h12 := consequence12 hm
  have h13 := consequence13 hm
  have h14 := consequence14 hm
  have h15 := consequence15 hm
  have h16 := consequence16 hm
  have h17 := consequence17 hm
  have h18 := consequence18 hm
  have h19 := consequence19 hm
  unfold Domain
  refine ⟨?_ ,?_ ,?_ ,?_⟩ <;>
    linarith only [hm.nq0,hm.nq1,hm.nq2,hm.nq3,hm.nq4,hm.nq5,hm.nq6,hm.nq7,hm.nq8,hm.nq9,hm.nr0,hm.nr1,hm.nr2,hm.nr3,hm.nr4,hm.nr5,hm.nr6,hm.nr7,hm.nr8,hm.nr9,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19]

theorem reconstruct (a b g : ℝ) (h : Domain a b g) :
    Moment (bottomProb a b g) (topProb a b g) := by
  obtain ⟨h0,h1,h2,h3⟩ := h
  change MomentSystem (bottomProb a b g ⟨0,by decide⟩) (bottomProb a b g ⟨1,by decide⟩) (bottomProb a b g ⟨2,by decide⟩) (bottomProb a b g ⟨3,by decide⟩) (bottomProb a b g ⟨4,by decide⟩) (bottomProb a b g ⟨5,by decide⟩) (bottomProb a b g ⟨6,by decide⟩) (bottomProb a b g ⟨7,by decide⟩) (bottomProb a b g ⟨8,by decide⟩) (bottomProb a b g ⟨9,by decide⟩) (topProb a b g ⟨0,by decide⟩) (topProb a b g ⟨1,by decide⟩) (topProb a b g ⟨2,by decide⟩) (topProb a b g ⟨3,by decide⟩) (topProb a b g ⟨4,by decide⟩) (topProb a b g ⟨5,by decide⟩) (topProb a b g ⟨6,by decide⟩) (topProb a b g ⟨7,by decide⟩) (topProb a b g ⟨8,by decide⟩) (topProb a b g ⟨9,by decide⟩)
  constructor <;> norm_num [bottomProb,topProb] <;> linarith only [h0,h1,h2,h3]

theorem complete_iff (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) :
    Moment p q ↔ ∃ a b g : ℝ, Domain a b g ∧ p=bottomProb a b g ∧ q=topProb a b g := by
  constructor
  · intro hm
    exact ⟨(p ⟨4,by decide⟩),(p ⟨6,by decide⟩),(p ⟨8,by decide⟩),domain_of_moment p q hm,normal_coordinates p q hm⟩
  · rintro ⟨a,b,g,hd,hp,hq⟩
    rw [hp,hq]
    exact reconstruct a b g hd

theorem actual_matched_flip : ∀ i,
    top i=SS.bxor (bottom i) (SS.stdBasis ⟨5,by decide⟩) := by decide +kernel

theorem matched_probabilities (p q : Fin 10 → ℝ) (hm : Moment p q) : p=q := by
  obtain ⟨hp,hq⟩ := normal_coordinates p q hm
  exact hp.trans hq.symm

theorem physical_normal_form (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∃ a b g : ℝ, Domain a b g ∧
      (fun i => Complex.normSq (c (bottom i)))=bottomProb a b g ∧
      (fun i => Complex.normSq (d (top i)))=topProb a b g := by
  apply (complete_iff _ _).1
  exact moments c d hc hd hnc hnd hkl
end Orbit43

namespace Orbit44
open SixQubit.Orbit44
def bottom : Fin 10 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9]
def top : Fin 10 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9]
def bottomProb (a b g : ℝ) : Fin 10 → ℝ := ![-a - g + 1/4,-a - g + 1/4,a,a,1/4 - b,1/4 - b,b,b,g,g]
def topProb (a b g : ℝ) : Fin 10 → ℝ := ![-a - g + 1/4,-a - g + 1/4,a,a,1/4 - b,1/4 - b,b,b,g,g]
def Domain (a b g : ℝ) : Prop := 0≤(a) ∧ 0≤(b) ∧ 0≤(g) ∧ 0≤(-a - g + 1/4) ∧ 0≤(1/4 - b)
def Moment (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) := MomentSystem (p ⟨0,by decide⟩) (p ⟨1,by decide⟩) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨4,by decide⟩) (p ⟨5,by decide⟩) (p ⟨6,by decide⟩) (p ⟨7,by decide⟩) (p ⟨8,by decide⟩) (p ⟨9,by decide⟩) (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩)
theorem actual_words :
    (∀ i, bottom i=MainTheory.OrderEightSupportDisplays.bits (![0,6,9,15,26,28,42,44,49,55] i)) ∧
    (∀ i, top i=MainTheory.OrderEightSupportDisplays.bits (![2,4,11,13,24,30,40,46,51,53] i)) ∧
    S0=Finset.univ.image bottom ∧ S1=Finset.univ.image top := by decide +kernel

theorem consequence0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q0=-q2 - q8 + 1/4 := by
  linear_combination 1 * hm.n0 + (-3/4) * hm.n1 + (-1/4) * hm.m1 + (-1/4) * hm.m2 + (-1/2) * hm.m3 + (-3/4) * hm.m4 + (-3/4) * hm.m5 + (1/2) * hm.m6 + (1/6) * hm.m14 + (1/6) * hm.m15 + (1/6) * hm.m24 + (1/6) * hm.m25 + (1/3) * hm.m34 + (1/3) * hm.m35 + (1/2) * hm.m45 + (-1/3) * hm.m46 + (-1/3) * hm.m56

theorem consequence1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q1=-q2 - q8 + 1/4 := by
  linear_combination (1/4) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/6) * hm.m3 + (1/4) * hm.m4 + (1/4) * hm.m5 + (5/6) * hm.m6 + (-1/6) * hm.m14 + (-1/6) * hm.m15 + (-1/6) * hm.m24 + (-1/6) * hm.m25 + (-1/3) * hm.m34 + (-1/3) * hm.m35 + (1/2) * hm.m45 + (-2/3) * hm.m46 + (-2/3) * hm.m56

theorem consequence2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q2=q2 := by
  ring

theorem consequence3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q3=q2 := by
  linear_combination (1/3) * hm.m1 + (1/3) * hm.m2 + (-1/3) * hm.m3 + (-2/3) * hm.m6 + (-1/3) * hm.m14 + (-1/3) * hm.m15 + (-1/3) * hm.m24 + (-1/3) * hm.m25 + (1/3) * hm.m34 + (1/3) * hm.m35 + (2/3) * hm.m46 + (2/3) * hm.m56

theorem consequence4 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q4=1/4 - q6 := by
  linear_combination (1/4) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/6) * hm.m3 + (1/4) * hm.m4 + (1/4) * hm.m5 + (-1/6) * hm.m6 + (-1/6) * hm.m14 + (1/6) * hm.m15 + (-1/6) * hm.m24 + (1/6) * hm.m25 + (-1/3) * hm.m34 + (1/3) * hm.m35 + (-1/2) * hm.m45 + (1/3) * hm.m46 + (-1/3) * hm.m56

theorem consequence5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q5=1/4 - q6 := by
  linear_combination (1/4) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/6) * hm.m3 + (1/4) * hm.m4 + (1/4) * hm.m5 + (-1/6) * hm.m6 + (-1/2) * hm.m14 + (1/2) * hm.m15 + (1/2) * hm.m24 + (-1/2) * hm.m25 + (-1/2) * hm.m45

theorem consequence6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q6=q6 := by
  ring

theorem consequence7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q7=q6 := by
  linear_combination (2/3) * hm.m14 + (-2/3) * hm.m15 + (-1/3) * hm.m24 + (1/3) * hm.m25 + (1/3) * hm.m34 + (-1/3) * hm.m35 + (-1/3) * hm.m46 + (1/3) * hm.m56

theorem consequence8 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q8=q8 := by
  ring

theorem consequence9 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q9=q8 := by
  linear_combination (-1/3) * hm.m1 + (-1/3) * hm.m2 + (1/3) * hm.m3 + (-1/3) * hm.m6 + (1/3) * hm.m14 + (1/3) * hm.m15 + (1/3) * hm.m24 + (1/3) * hm.m25 + (-1/3) * hm.m34 + (-1/3) * hm.m35 + (1/3) * hm.m46 + (1/3) * hm.m56

theorem consequence10 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r0=-q2 - q8 + 1/4 := by
  linear_combination (1/4) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/6) * hm.m3 + (1/4) * hm.m4 + (-3/4) * hm.m5 + (5/6) * hm.m6 + (-1/6) * hm.m14 + (1/6) * hm.m15 + (-1/6) * hm.m24 + (1/6) * hm.m25 + (-1/3) * hm.m34 + (1/3) * hm.m35 + (1/2) * hm.m45 + (-2/3) * hm.m46 + (-1/3) * hm.m56

theorem consequence11 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r1=-q2 - q8 + 1/4 := by
  linear_combination (1/4) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/6) * hm.m3 + (-3/4) * hm.m4 + (1/4) * hm.m5 + (5/6) * hm.m6 + (1/6) * hm.m14 + (-1/6) * hm.m15 + (1/6) * hm.m24 + (-1/6) * hm.m25 + (1/3) * hm.m34 + (-1/3) * hm.m35 + (1/2) * hm.m45 + (-1/3) * hm.m46 + (-2/3) * hm.m56

theorem consequence12 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r2=q2 := by
  linear_combination (1/3) * hm.m1 + (1/3) * hm.m2 + (-1/3) * hm.m3 + (-2/3) * hm.m6 + (-1/3) * hm.m14 + (-1/3) * hm.m24 + (1/3) * hm.m34 + (2/3) * hm.m46

theorem consequence13 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r3=q2 := by
  linear_combination (1/3) * hm.m1 + (1/3) * hm.m2 + (-1/3) * hm.m3 + (-2/3) * hm.m6 + (-1/3) * hm.m15 + (-1/3) * hm.m25 + (1/3) * hm.m35 + (2/3) * hm.m56

theorem consequence14 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r4=1/4 - q6 := by
  linear_combination (1/4) * hm.n1 + (5/12) * hm.m1 + (-7/12) * hm.m2 + (-1/6) * hm.m3 + (1/4) * hm.m4 + (1/4) * hm.m5 + (1/6) * hm.m6 + (-1/2) * hm.m14 + (1/6) * hm.m15 + (1/2) * hm.m24 + (1/6) * hm.m25 + (1/3) * hm.m35 + (-1/2) * hm.m45 + (-1/3) * hm.m56

theorem consequence15 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r5=1/4 - q6 := by
  linear_combination (1/4) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/6) * hm.m3 + (1/4) * hm.m4 + (1/4) * hm.m5 + (-1/6) * hm.m6 + (-1/6) * hm.m14 + (1/2) * hm.m15 + (-1/6) * hm.m24 + (-1/2) * hm.m25 + (-1/3) * hm.m34 + (-1/2) * hm.m45 + (1/3) * hm.m46

theorem consequence16 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r6=q6 := by
  linear_combination (-2/3) * hm.m1 + (1/3) * hm.m2 + (-1/3) * hm.m3 + (1/3) * hm.m6 + (2/3) * hm.m14 + (-1/3) * hm.m24 + (1/3) * hm.m34 + (-1/3) * hm.m46

theorem consequence17 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r7=q6 := by
  linear_combination (-2/3) * hm.m15 + (1/3) * hm.m25 + (-1/3) * hm.m35 + (1/3) * hm.m56

theorem consequence18 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r8=q8 := by
  linear_combination (-1/3) * hm.m1 + (-1/3) * hm.m2 + (1/3) * hm.m3 + (-1/3) * hm.m6 + (1/3) * hm.m14 + (1/3) * hm.m24 + (-1/3) * hm.m34 + (1/3) * hm.m46

theorem consequence19 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r9=q8 := by
  linear_combination (-1/3) * hm.m1 + (-1/3) * hm.m2 + (1/3) * hm.m3 + (-1/3) * hm.m6 + (1/3) * hm.m15 + (1/3) * hm.m25 + (-1/3) * hm.m35 + (1/3) * hm.m56

theorem normal_coordinates (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) (hm : Moment p q) :
    p=bottomProb (p ⟨2,by decide⟩) (p ⟨6,by decide⟩) (p ⟨8,by decide⟩) ∧ q=topProb (p ⟨2,by decide⟩) (p ⟨6,by decide⟩) (p ⟨8,by decide⟩) := by
  have h0 := consequence0 hm
  have h1 := consequence1 hm
  have h2 := consequence2 hm
  have h3 := consequence3 hm
  have h4 := consequence4 hm
  have h5 := consequence5 hm
  have h6 := consequence6 hm
  have h7 := consequence7 hm
  have h8 := consequence8 hm
  have h9 := consequence9 hm
  have h10 := consequence10 hm
  have h11 := consequence11 hm
  have h12 := consequence12 hm
  have h13 := consequence13 hm
  have h14 := consequence14 hm
  have h15 := consequence15 hm
  have h16 := consequence16 hm
  have h17 := consequence17 hm
  have h18 := consequence18 hm
  have h19 := consequence19 hm
  constructor
  · ext i
    fin_cases i <;> norm_num [bottomProb,Fin.succ] at * <;> linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19]
  · ext i
    fin_cases i <;> norm_num [topProb,Fin.succ] at * <;> linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19]

theorem domain_of_moment (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) (hm : Moment p q) : Domain (p ⟨2,by decide⟩) (p ⟨6,by decide⟩) (p ⟨8,by decide⟩) := by
  have h0 := consequence0 hm
  have h1 := consequence1 hm
  have h2 := consequence2 hm
  have h3 := consequence3 hm
  have h4 := consequence4 hm
  have h5 := consequence5 hm
  have h6 := consequence6 hm
  have h7 := consequence7 hm
  have h8 := consequence8 hm
  have h9 := consequence9 hm
  have h10 := consequence10 hm
  have h11 := consequence11 hm
  have h12 := consequence12 hm
  have h13 := consequence13 hm
  have h14 := consequence14 hm
  have h15 := consequence15 hm
  have h16 := consequence16 hm
  have h17 := consequence17 hm
  have h18 := consequence18 hm
  have h19 := consequence19 hm
  unfold Domain
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_⟩ <;>
    linarith only [hm.nq0,hm.nq1,hm.nq2,hm.nq3,hm.nq4,hm.nq5,hm.nq6,hm.nq7,hm.nq8,hm.nq9,hm.nr0,hm.nr1,hm.nr2,hm.nr3,hm.nr4,hm.nr5,hm.nr6,hm.nr7,hm.nr8,hm.nr9,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19]

theorem reconstruct (a b g : ℝ) (h : Domain a b g) :
    Moment (bottomProb a b g) (topProb a b g) := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := h
  change MomentSystem (bottomProb a b g ⟨0,by decide⟩) (bottomProb a b g ⟨1,by decide⟩) (bottomProb a b g ⟨2,by decide⟩) (bottomProb a b g ⟨3,by decide⟩) (bottomProb a b g ⟨4,by decide⟩) (bottomProb a b g ⟨5,by decide⟩) (bottomProb a b g ⟨6,by decide⟩) (bottomProb a b g ⟨7,by decide⟩) (bottomProb a b g ⟨8,by decide⟩) (bottomProb a b g ⟨9,by decide⟩) (topProb a b g ⟨0,by decide⟩) (topProb a b g ⟨1,by decide⟩) (topProb a b g ⟨2,by decide⟩) (topProb a b g ⟨3,by decide⟩) (topProb a b g ⟨4,by decide⟩) (topProb a b g ⟨5,by decide⟩) (topProb a b g ⟨6,by decide⟩) (topProb a b g ⟨7,by decide⟩) (topProb a b g ⟨8,by decide⟩) (topProb a b g ⟨9,by decide⟩)
  constructor <;> norm_num [bottomProb,topProb] <;> linarith only [h0,h1,h2,h3,h4]

theorem complete_iff (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) :
    Moment p q ↔ ∃ a b g : ℝ, Domain a b g ∧ p=bottomProb a b g ∧ q=topProb a b g := by
  constructor
  · intro hm
    exact ⟨(p ⟨2,by decide⟩),(p ⟨6,by decide⟩),(p ⟨8,by decide⟩),domain_of_moment p q hm,normal_coordinates p q hm⟩
  · rintro ⟨a,b,g,hd,hp,hq⟩
    rw [hp,hq]
    exact reconstruct a b g hd

theorem actual_matched_flip : ∀ i,
    top i=SS.bxor (bottom i) (SS.stdBasis ⟨4,by decide⟩) := by decide +kernel

theorem matched_probabilities (p q : Fin 10 → ℝ) (hm : Moment p q) : p=q := by
  obtain ⟨hp,hq⟩ := normal_coordinates p q hm
  exact hp.trans hq.symm

theorem physical_normal_form (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∃ a b g : ℝ, Domain a b g ∧
      (fun i => Complex.normSq (c (bottom i)))=bottomProb a b g ∧
      (fun i => Complex.normSq (d (top i)))=topProb a b g := by
  apply (complete_iff _ _).1
  exact moments c d hc hd hnc hnd hkl
end Orbit44

namespace Orbit46
open SixQubit.Orbit46
def bottom : Fin 10 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9]
def top : Fin 10 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9]
def bottomProb (a b g : ℝ) : Fin 10 → ℝ := ![1/4 - a,1/4 - a,a,a,-b - g + 1/4,-b - g + 1/4,b,b,g,g]
def topProb (a b g : ℝ) : Fin 10 → ℝ := ![1/4 - a,1/4 - a,a,a,-b - g + 1/4,-b - g + 1/4,b,b,g,g]
def Domain (a b g : ℝ) : Prop := 0≤(a) ∧ 0≤(b) ∧ 0≤(g) ∧ 0≤(1/4 - a) ∧ 0≤(-b - g + 1/4)
def Moment (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) := MomentSystem (p ⟨0,by decide⟩) (p ⟨1,by decide⟩) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨4,by decide⟩) (p ⟨5,by decide⟩) (p ⟨6,by decide⟩) (p ⟨7,by decide⟩) (p ⟨8,by decide⟩) (p ⟨9,by decide⟩) (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩)
theorem actual_words :
    (∀ i, bottom i=MainTheory.OrderEightSupportDisplays.bits (![0,3,28,31,37,38,41,42,49,50] i)) ∧
    (∀ i, top i=MainTheory.OrderEightSupportDisplays.bits (![1,2,29,30,36,39,40,43,48,51] i)) ∧
    S0=Finset.univ.image bottom ∧ S1=Finset.univ.image top := by decide +kernel

theorem consequence0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q0=1/4 - q2 := by
  linear_combination 1 * hm.n0 + (-3/4) * hm.n1 + (-3/4) * hm.m1 + (-3/4) * hm.m5 + (-3/4) * hm.m6 + (1/2) * hm.m15 + (1/2) * hm.m16 + (1/2) * hm.m56

theorem consequence1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q1=1/4 - q2 := by
  linear_combination (1/4) * hm.n1 + (-1/12) * hm.m1 + (1/3) * hm.m2 + (1/3) * hm.m3 + (1/3) * hm.m4 + (1/4) * hm.m5 + (1/4) * hm.m6 + (-1/6) * hm.m15 + (-1/6) * hm.m16 + (-1/3) * hm.m25 + (-1/3) * hm.m26 + (-1/3) * hm.m35 + (-1/3) * hm.m36 + (-1/3) * hm.m45 + (-1/3) * hm.m46 + (1/2) * hm.m56

theorem consequence2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q2=q2 := by
  ring

theorem consequence3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q3=q2 := by
  linear_combination (1/3) * hm.m1 + (-1/3) * hm.m2 + (-1/3) * hm.m3 + (-1/3) * hm.m4 + (-1/3) * hm.m15 + (-1/3) * hm.m16 + (1/3) * hm.m25 + (1/3) * hm.m26 + (1/3) * hm.m35 + (1/3) * hm.m36 + (1/3) * hm.m45 + (1/3) * hm.m46

theorem consequence4 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q4=-q6 - q8 + 1/4 := by
  linear_combination (1/4) * hm.n1 + (1/4) * hm.m1 + (1/4) * hm.m5 + (1/4) * hm.m6 + (-1/2) * hm.m15 + (1/2) * hm.m16 + (-1/2) * hm.m56

theorem consequence5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q5=-q6 - q8 + 1/4 := by
  linear_combination (1/4) * hm.n1 + (1/4) * hm.m1 + (1/4) * hm.m5 + (1/4) * hm.m6 + (-1/6) * hm.m15 + (1/6) * hm.m16 + (-1/3) * hm.m25 + (1/3) * hm.m26 + (-1/3) * hm.m35 + (1/3) * hm.m36 + (2/3) * hm.m45 + (-2/3) * hm.m46 + (-1/2) * hm.m56

theorem consequence6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q6=q6 := by
  ring

theorem consequence7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q7=q6 := by
  linear_combination (1/3) * hm.m15 + (-1/3) * hm.m16 + (-1/3) * hm.m25 + (1/3) * hm.m26 + (2/3) * hm.m35 + (-2/3) * hm.m36 + (-1/3) * hm.m45 + (1/3) * hm.m46

theorem consequence8 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q8=q8 := by
  ring

theorem consequence9 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q9=q8 := by
  linear_combination (1/3) * hm.m15 + (-1/3) * hm.m16 + (2/3) * hm.m25 + (-2/3) * hm.m26 + (-1/3) * hm.m35 + (1/3) * hm.m36 + (-1/3) * hm.m45 + (1/3) * hm.m46

theorem consequence10 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r0=1/4 - q2 := by
  linear_combination (1/4) * hm.n1 + (-1/12) * hm.m1 + (1/3) * hm.m2 + (1/3) * hm.m3 + (1/3) * hm.m4 + (1/4) * hm.m5 + (-3/4) * hm.m6 + (-1/6) * hm.m15 + (1/2) * hm.m16 + (-1/3) * hm.m25 + (-1/3) * hm.m35 + (-1/3) * hm.m45 + (1/2) * hm.m56

theorem consequence11 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r1=1/4 - q2 := by
  linear_combination (1/4) * hm.n1 + (-1/12) * hm.m1 + (1/3) * hm.m2 + (1/3) * hm.m3 + (1/3) * hm.m4 + (-3/4) * hm.m5 + (1/4) * hm.m6 + (1/2) * hm.m15 + (-1/6) * hm.m16 + (-1/3) * hm.m26 + (-1/3) * hm.m36 + (-1/3) * hm.m46 + (1/2) * hm.m56

theorem consequence12 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r2=q2 := by
  linear_combination (1/3) * hm.m1 + (-1/3) * hm.m2 + (-1/3) * hm.m3 + (-1/3) * hm.m4 + (-1/3) * hm.m15 + (1/3) * hm.m25 + (1/3) * hm.m35 + (1/3) * hm.m45

theorem consequence13 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r3=q2 := by
  linear_combination (1/3) * hm.m1 + (-1/3) * hm.m2 + (-1/3) * hm.m3 + (-1/3) * hm.m4 + (-1/3) * hm.m16 + (1/3) * hm.m26 + (1/3) * hm.m36 + (1/3) * hm.m46

theorem consequence14 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r4=-q6 - q8 + 1/4 := by
  linear_combination (1/4) * hm.n1 + (-1/12) * hm.m1 + (1/3) * hm.m2 + (1/3) * hm.m3 + (-2/3) * hm.m4 + (1/4) * hm.m5 + (1/4) * hm.m6 + (-1/6) * hm.m15 + (1/2) * hm.m16 + (-1/3) * hm.m25 + (-1/3) * hm.m35 + (2/3) * hm.m45 + (-1/2) * hm.m56

theorem consequence15 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r5=-q6 - q8 + 1/4 := by
  linear_combination (1/4) * hm.n1 + (1/4) * hm.m1 + (1/4) * hm.m5 + (1/4) * hm.m6 + (-1/2) * hm.m15 + (1/6) * hm.m16 + (1/3) * hm.m26 + (1/3) * hm.m36 + (-2/3) * hm.m46 + (-1/2) * hm.m56

theorem consequence16 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r6=q6 := by
  linear_combination (-1/3) * hm.m1 + (1/3) * hm.m2 + (-2/3) * hm.m3 + (1/3) * hm.m4 + (1/3) * hm.m15 + (-1/3) * hm.m25 + (2/3) * hm.m35 + (-1/3) * hm.m45

theorem consequence17 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r7=q6 := by
  linear_combination (-1/3) * hm.m16 + (1/3) * hm.m26 + (-2/3) * hm.m36 + (1/3) * hm.m46

theorem consequence18 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r8=q8 := by
  linear_combination (-1/3) * hm.m1 + (-2/3) * hm.m2 + (1/3) * hm.m3 + (1/3) * hm.m4 + (1/3) * hm.m15 + (2/3) * hm.m25 + (-1/3) * hm.m35 + (-1/3) * hm.m45

theorem consequence19 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r9=q8 := by
  linear_combination (-1/3) * hm.m16 + (-2/3) * hm.m26 + (1/3) * hm.m36 + (1/3) * hm.m46

theorem normal_coordinates (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) (hm : Moment p q) :
    p=bottomProb (p ⟨2,by decide⟩) (p ⟨6,by decide⟩) (p ⟨8,by decide⟩) ∧ q=topProb (p ⟨2,by decide⟩) (p ⟨6,by decide⟩) (p ⟨8,by decide⟩) := by
  have h0 := consequence0 hm
  have h1 := consequence1 hm
  have h2 := consequence2 hm
  have h3 := consequence3 hm
  have h4 := consequence4 hm
  have h5 := consequence5 hm
  have h6 := consequence6 hm
  have h7 := consequence7 hm
  have h8 := consequence8 hm
  have h9 := consequence9 hm
  have h10 := consequence10 hm
  have h11 := consequence11 hm
  have h12 := consequence12 hm
  have h13 := consequence13 hm
  have h14 := consequence14 hm
  have h15 := consequence15 hm
  have h16 := consequence16 hm
  have h17 := consequence17 hm
  have h18 := consequence18 hm
  have h19 := consequence19 hm
  constructor
  · ext i
    fin_cases i <;> norm_num [bottomProb,Fin.succ] at * <;> linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19]
  · ext i
    fin_cases i <;> norm_num [topProb,Fin.succ] at * <;> linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19]

theorem domain_of_moment (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) (hm : Moment p q) : Domain (p ⟨2,by decide⟩) (p ⟨6,by decide⟩) (p ⟨8,by decide⟩) := by
  have h0 := consequence0 hm
  have h1 := consequence1 hm
  have h2 := consequence2 hm
  have h3 := consequence3 hm
  have h4 := consequence4 hm
  have h5 := consequence5 hm
  have h6 := consequence6 hm
  have h7 := consequence7 hm
  have h8 := consequence8 hm
  have h9 := consequence9 hm
  have h10 := consequence10 hm
  have h11 := consequence11 hm
  have h12 := consequence12 hm
  have h13 := consequence13 hm
  have h14 := consequence14 hm
  have h15 := consequence15 hm
  have h16 := consequence16 hm
  have h17 := consequence17 hm
  have h18 := consequence18 hm
  have h19 := consequence19 hm
  unfold Domain
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_⟩ <;>
    linarith only [hm.nq0,hm.nq1,hm.nq2,hm.nq3,hm.nq4,hm.nq5,hm.nq6,hm.nq7,hm.nq8,hm.nq9,hm.nr0,hm.nr1,hm.nr2,hm.nr3,hm.nr4,hm.nr5,hm.nr6,hm.nr7,hm.nr8,hm.nr9,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19]

theorem reconstruct (a b g : ℝ) (h : Domain a b g) :
    Moment (bottomProb a b g) (topProb a b g) := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := h
  change MomentSystem (bottomProb a b g ⟨0,by decide⟩) (bottomProb a b g ⟨1,by decide⟩) (bottomProb a b g ⟨2,by decide⟩) (bottomProb a b g ⟨3,by decide⟩) (bottomProb a b g ⟨4,by decide⟩) (bottomProb a b g ⟨5,by decide⟩) (bottomProb a b g ⟨6,by decide⟩) (bottomProb a b g ⟨7,by decide⟩) (bottomProb a b g ⟨8,by decide⟩) (bottomProb a b g ⟨9,by decide⟩) (topProb a b g ⟨0,by decide⟩) (topProb a b g ⟨1,by decide⟩) (topProb a b g ⟨2,by decide⟩) (topProb a b g ⟨3,by decide⟩) (topProb a b g ⟨4,by decide⟩) (topProb a b g ⟨5,by decide⟩) (topProb a b g ⟨6,by decide⟩) (topProb a b g ⟨7,by decide⟩) (topProb a b g ⟨8,by decide⟩) (topProb a b g ⟨9,by decide⟩)
  constructor <;> norm_num [bottomProb,topProb] <;> linarith only [h0,h1,h2,h3,h4]

theorem complete_iff (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) :
    Moment p q ↔ ∃ a b g : ℝ, Domain a b g ∧ p=bottomProb a b g ∧ q=topProb a b g := by
  constructor
  · intro hm
    exact ⟨(p ⟨2,by decide⟩),(p ⟨6,by decide⟩),(p ⟨8,by decide⟩),domain_of_moment p q hm,normal_coordinates p q hm⟩
  · rintro ⟨a,b,g,hd,hp,hq⟩
    rw [hp,hq]
    exact reconstruct a b g hd

theorem actual_matched_flip : ∀ i,
    top i=SS.bxor (bottom i) (SS.stdBasis ⟨5,by decide⟩) := by decide +kernel

theorem matched_probabilities (p q : Fin 10 → ℝ) (hm : Moment p q) : p=q := by
  obtain ⟨hp,hq⟩ := normal_coordinates p q hm
  exact hp.trans hq.symm

theorem physical_normal_form (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∃ a b g : ℝ, Domain a b g ∧
      (fun i => Complex.normSq (c (bottom i)))=bottomProb a b g ∧
      (fun i => Complex.normSq (d (top i)))=topProb a b g := by
  apply (complete_iff _ _).1
  exact moments c d hc hd hnc hnd hkl
end Orbit46

end
end MainTheory.OrderTwoPrintedMoments
