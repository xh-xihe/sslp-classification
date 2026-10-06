import SixQubit.CodeOrbit47
import SixQubit.CodeOrbit48
import SixQubit.CodeOrbit49
import SixQubit.CodeOrbit50
import SixQubit.CodeOrbit51
import SixQubit.CodeOrbit52
import MainTheory.OrderEightSupportDisplays

/-! Both directions of the literal SI probability normal forms, over ℝ.
The rational row combinations are checked against the actual native moments.
The source words and both probability boundaries are retained explicitly.
No final no-code theorem is used to derive any normal form.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.OrderThreePrintedMoments
noncomputable section

namespace Orbit47
open SixQubit.Orbit47
def bottom : Fin 9 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8]
def top : Fin 9 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8]
def bottomProb (a b : ℝ) : Fin 9 → ℝ := ![1/3,b,a,-a - b + 1/6,-a - b + 1/6,a,b,1/6,1/6]
def topProb (a b : ℝ) : Fin 9 → ℝ := ![1/6,1/6,b,a,-a - b + 1/6,-a - b + 1/6,a,b,1/3]
def Domain (a b : ℝ) : Prop := 0≤(a) ∧ 0≤(b) ∧ 0≤(-a - b + 1/6)
def Moment (p : Fin 9 → ℝ) (q : Fin 9 → ℝ) := MomentSystem (p ⟨0,by decide⟩) (p ⟨1,by decide⟩) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨4,by decide⟩) (p ⟨5,by decide⟩) (p ⟨6,by decide⟩) (p ⟨7,by decide⟩) (p ⟨8,by decide⟩) (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩)
theorem actual_words :
    (∀ i, bottom i=MainTheory.OrderEightSupportDisplays.bits (![0,15,23,27,39,43,51,61,62] i)) ∧
    (∀ i, top i=MainTheory.OrderEightSupportDisplays.bits (![1,2,12,20,24,36,40,48,63] i)) ∧
    S0=Finset.univ.image bottom ∧ S1=Finset.univ.image top := by decide +kernel

theorem consequence0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q0=1/3 := by
  linear_combination 1 * hm.n0 + (-2/3) * hm.n1 + (-1/3) * hm.m1 + (-1/3) * hm.m2 + (-1/3) * hm.m3 + (-1/3) * hm.m4 + (-2/3) * hm.m5 + (-2/3) * hm.m6 + (-1/2) * hm.m15 + 1 * hm.m16 + (1/2) * hm.m25 + (1/2) * hm.m35 + (1/2) * hm.m45

theorem consequence1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q1=q1 := by
  ring

theorem consequence2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q2=q2 := by
  ring

theorem consequence3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q3=-q1 - q2 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/12) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (-1/4) * hm.m12 + (-1/4) * hm.m13 + (-1/4) * hm.m14 + (-3/4) * hm.m15 + (1/4) * hm.m25 + (1/4) * hm.m35 + (1/4) * hm.m45

theorem consequence4 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q4=-q1 - q2 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/12) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (-1/4) * hm.m12 + (-1/4) * hm.m13 + (-1/4) * hm.m14 + (-1/4) * hm.m15 + (-1/4) * hm.m25 + (-1/4) * hm.m35 + (3/4) * hm.m45

theorem consequence5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q5=q2 := by
  linear_combination (1/2) * hm.m15 + (-1/2) * hm.m25 + (1/2) * hm.m35 + (-1/2) * hm.m45

theorem consequence6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q6=q1 := by
  linear_combination (1/2) * hm.m15 + (1/2) * hm.m25 + (-1/2) * hm.m35 + (-1/2) * hm.m45

theorem consequence7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q7=1/6 := by
  linear_combination (1/6) * hm.n1 + (-1/6) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/12) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (1/4) * hm.m12 + (1/4) * hm.m13 + (1/4) * hm.m14 + (-1/4) * hm.m15 + (-1/4) * hm.m25 + (-1/4) * hm.m35 + (-1/4) * hm.m45

theorem consequence8 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q8=1/6 := by
  linear_combination (1/6) * hm.n1 + (-1/6) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/12) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (1/4) * hm.m12 + (1/4) * hm.m13 + (1/4) * hm.m14 + (3/4) * hm.m15 + -1 * hm.m16 + (-1/4) * hm.m25 + (-1/4) * hm.m35 + (-1/4) * hm.m45

theorem consequence9 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) : r0=1/6 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/12) * hm.m4 + (1/6) * hm.m5 + (-5/6) * hm.m6 + (-1/4) * hm.m12 + (-1/4) * hm.m13 + (-1/4) * hm.m14 + (-3/4) * hm.m15 + 1 * hm.m16 + (1/4) * hm.m25 + (1/4) * hm.m35 + (1/4) * hm.m45

theorem consequence10 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) : r1=1/6 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/12) * hm.m4 + (-5/6) * hm.m5 + (1/6) * hm.m6 + (-1/4) * hm.m12 + (-1/4) * hm.m13 + (-1/4) * hm.m14 + (1/4) * hm.m15 + (1/4) * hm.m25 + (1/4) * hm.m35 + (1/4) * hm.m45

theorem consequence11 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) : r2=q1 := by
  linear_combination (1/2) * hm.m2 + (-1/2) * hm.m3 + (-1/2) * hm.m4 + (-1/2) * hm.m12 + (1/2) * hm.m13 + (1/2) * hm.m14

theorem consequence12 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) : r3=q2 := by
  linear_combination (-1/2) * hm.m2 + (1/2) * hm.m3 + (-1/2) * hm.m4 + (1/2) * hm.m12 + (-1/2) * hm.m13 + (1/2) * hm.m14

theorem consequence13 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) : r4=-q1 - q2 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (-5/12) * hm.m2 + (-5/12) * hm.m3 + (7/12) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (1/4) * hm.m12 + (1/4) * hm.m13 + (-3/4) * hm.m14 + (-3/4) * hm.m15 + (1/4) * hm.m25 + (1/4) * hm.m35 + (1/4) * hm.m45

theorem consequence14 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) : r5=-q1 - q2 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (-1/6) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/12) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (1/4) * hm.m12 + (1/4) * hm.m13 + (-3/4) * hm.m14 + (-1/4) * hm.m15 + (-1/4) * hm.m25 + (-1/4) * hm.m35 + (3/4) * hm.m45

theorem consequence15 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) : r6=q2 := by
  linear_combination (-1/2) * hm.m1 + (1/2) * hm.m12 + (-1/2) * hm.m13 + (1/2) * hm.m14 + (1/2) * hm.m15 + (-1/2) * hm.m25 + (1/2) * hm.m35 + (-1/2) * hm.m45

theorem consequence16 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) : r7=q1 := by
  linear_combination (-1/2) * hm.m1 + (-1/2) * hm.m12 + (1/2) * hm.m13 + (1/2) * hm.m14 + (1/2) * hm.m15 + (1/2) * hm.m25 + (-1/2) * hm.m35 + (-1/2) * hm.m45

theorem consequence17 {q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 r0 r1 r2 r3 r4 r5 r6 r7 r8) : r8=1/3 := by
  linear_combination (1/3) * hm.n1 + (1/6) * hm.m1 + (1/6) * hm.m2 + (1/6) * hm.m3 + (1/6) * hm.m4 + (1/3) * hm.m5 + (1/3) * hm.m6 + (1/2) * hm.m15 + -1 * hm.m16 + (-1/2) * hm.m25 + (-1/2) * hm.m35 + (-1/2) * hm.m45

theorem normal_coordinates (p : Fin 9 → ℝ) (q : Fin 9 → ℝ) (hm : Moment p q) :
    p=bottomProb (p ⟨2,by decide⟩) (p ⟨1,by decide⟩) ∧ q=topProb (p ⟨2,by decide⟩) (p ⟨1,by decide⟩) := by
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
  constructor
  · ext i
    fin_cases i <;> norm_num [bottomProb,Fin.succ] at * <;> linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17]
  · ext i
    fin_cases i <;> norm_num [topProb,Fin.succ] at * <;> linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17]

theorem domain_of_moment (p : Fin 9 → ℝ) (q : Fin 9 → ℝ) (hm : Moment p q) : Domain (p ⟨2,by decide⟩) (p ⟨1,by decide⟩) := by
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
  unfold Domain
  refine ⟨?_ ,?_ ,?_⟩ <;>
    linarith only [hm.nq0,hm.nq1,hm.nq2,hm.nq3,hm.nq4,hm.nq5,hm.nq6,hm.nq7,hm.nq8,hm.nr0,hm.nr1,hm.nr2,hm.nr3,hm.nr4,hm.nr5,hm.nr6,hm.nr7,hm.nr8,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17]

theorem reconstruct (a b : ℝ) (h : Domain a b) :
    Moment (bottomProb a b) (topProb a b) := by
  obtain ⟨h0,h1,h2⟩ := h
  change MomentSystem (bottomProb a b ⟨0,by decide⟩) (bottomProb a b ⟨1,by decide⟩) (bottomProb a b ⟨2,by decide⟩) (bottomProb a b ⟨3,by decide⟩) (bottomProb a b ⟨4,by decide⟩) (bottomProb a b ⟨5,by decide⟩) (bottomProb a b ⟨6,by decide⟩) (bottomProb a b ⟨7,by decide⟩) (bottomProb a b ⟨8,by decide⟩) (topProb a b ⟨0,by decide⟩) (topProb a b ⟨1,by decide⟩) (topProb a b ⟨2,by decide⟩) (topProb a b ⟨3,by decide⟩) (topProb a b ⟨4,by decide⟩) (topProb a b ⟨5,by decide⟩) (topProb a b ⟨6,by decide⟩) (topProb a b ⟨7,by decide⟩) (topProb a b ⟨8,by decide⟩)
  constructor <;> norm_num [bottomProb,topProb] <;> linarith only [h0,h1,h2]

theorem complete_iff (p : Fin 9 → ℝ) (q : Fin 9 → ℝ) :
    Moment p q ↔ ∃ a b : ℝ, Domain a b ∧ p=bottomProb a b ∧ q=topProb a b := by
  constructor
  · intro hm
    exact ⟨(p ⟨2,by decide⟩),(p ⟨1,by decide⟩),domain_of_moment p q hm,normal_coordinates p q hm⟩
  · rintro ⟨a,b,hd,hp,hq⟩
    rw [hp,hq]
    exact reconstruct a b hd

theorem physical_normal_form (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∃ a b : ℝ, Domain a b ∧
      (fun i => Complex.normSq (c (bottom i)))=bottomProb a b ∧
      (fun i => Complex.normSq (d (top i)))=topProb a b := by
  apply (complete_iff _ _).1
  exact moments c d hc hd hnc hnd hkl
end Orbit47

namespace Orbit48
open SixQubit.Orbit48
def bottom : Fin 11 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10]
def top : Fin 9 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8]
def bottomProb (a b : ℝ) : Fin 11 → ℝ := ![1/3,1/6,-a/2 - b/2 + 1/6,-a/2 - b/2 + 1/6,-a/2 - b/2 + 1/6,a/2,a/2,a/2,b/2,b/2,b/2]
def topProb (a b : ℝ) : Fin 9 → ℝ := ![1/6,1/6,1/6,-a/2 - b/2 + 1/6,-a - b + 1/3,a/2,a,b/2,b]
def Domain (a b : ℝ) : Prop := 0≤(a) ∧ 0≤(b) ∧ 0≤(-a - b + 1/3)
def Moment (p : Fin 11 → ℝ) (q : Fin 9 → ℝ) := MomentSystem (p ⟨0,by decide⟩) (p ⟨1,by decide⟩) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨4,by decide⟩) (p ⟨5,by decide⟩) (p ⟨6,by decide⟩) (p ⟨7,by decide⟩) (p ⟨8,by decide⟩) (p ⟨9,by decide⟩) (p ⟨10,by decide⟩) (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩)
theorem actual_words :
    (∀ i, bottom i=MainTheory.OrderEightSupportDisplays.bits (![0,7,27,29,30,43,45,46,51,53,54] i)) ∧
    (∀ i, top i=MainTheory.OrderEightSupportDisplays.bits (![1,2,4,24,31,40,47,48,55] i)) ∧
    S0=Finset.univ.image bottom ∧ S1=Finset.univ.image top := by decide +kernel

theorem consequence0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q0=1/3 := by
  linear_combination 1 * hm.n0 + (-2/3) * hm.n1 + (-1/3) * hm.m1 + (-1/3) * hm.m2 + (-1/3) * hm.m3 + (-2/3) * hm.m4 + (-2/3) * hm.m5 + (-2/3) * hm.m6 + (1/2) * hm.m16 + (1/2) * hm.m26 + (1/2) * hm.m36 + 1 * hm.m45

theorem consequence1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q1=1/6 := by
  linear_combination (1/6) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/6) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (-1/4) * hm.m14 + (-1/4) * hm.m15 + (-1/4) * hm.m24 + (-1/4) * hm.m25 + (-1/4) * hm.m34 + (-1/4) * hm.m35 + (1/2) * hm.m45

theorem consequence2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q2=-r6/2 - r8/2 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/6) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (1/4) * hm.m14 + (-1/4) * hm.m15 + (-1/2) * hm.m16 + (-1/4) * hm.m24 + (1/4) * hm.m25 + (-1/4) * hm.m34 + (1/4) * hm.m35 + (-1/2) * hm.m45

theorem consequence3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q3=-r6/2 - r8/2 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/6) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (-1/4) * hm.m14 + (1/4) * hm.m15 + (-1/2) * hm.m16 + (1/4) * hm.m24 + (-1/4) * hm.m25 + (1/4) * hm.m34 + (-1/4) * hm.m35 + (-1/2) * hm.m45

theorem consequence4 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q4=-r6/2 - r8/2 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/6) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (-1/4) * hm.m14 + (-1/4) * hm.m15 + (1/4) * hm.m24 + (1/4) * hm.m25 + (-1/2) * hm.m26 + (1/4) * hm.m34 + (1/4) * hm.m35 + (-1/2) * hm.m36 + (-1/2) * hm.m45

theorem consequence5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q5=r6/2 := by
  linear_combination (-1/4) * hm.m14 + (1/4) * hm.m15 + (1/4) * hm.m16 + (1/4) * hm.m24 + (-1/4) * hm.m25 + (-1/4) * hm.m26 + (-1/4) * hm.m34 + (1/4) * hm.m35 + (1/4) * hm.m36

theorem consequence6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q6=r6/2 := by
  linear_combination (1/4) * hm.m14 + (-1/4) * hm.m15 + (1/4) * hm.m16 + (-1/4) * hm.m24 + (1/4) * hm.m25 + (-1/4) * hm.m26 + (1/4) * hm.m34 + (-1/4) * hm.m35 + (1/4) * hm.m36

theorem consequence7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q7=r6/2 := by
  linear_combination (1/4) * hm.m14 + (1/4) * hm.m15 + (-1/4) * hm.m16 + (-1/4) * hm.m24 + (-1/4) * hm.m25 + (1/4) * hm.m26 + (1/4) * hm.m34 + (1/4) * hm.m35 + (-1/4) * hm.m36

theorem consequence8 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q8=r8/2 := by
  linear_combination (-1/4) * hm.m14 + (1/4) * hm.m15 + (1/4) * hm.m16 + (-1/4) * hm.m24 + (1/4) * hm.m25 + (1/4) * hm.m26 + (1/4) * hm.m34 + (-1/4) * hm.m35 + (-1/4) * hm.m36

theorem consequence9 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q9=r8/2 := by
  linear_combination (1/4) * hm.m14 + (-1/4) * hm.m15 + (1/4) * hm.m16 + (1/4) * hm.m24 + (-1/4) * hm.m25 + (1/4) * hm.m26 + (-1/4) * hm.m34 + (1/4) * hm.m35 + (-1/4) * hm.m36

theorem consequence10 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : q10=r8/2 := by
  linear_combination (1/4) * hm.m14 + (1/4) * hm.m15 + (-1/4) * hm.m16 + (1/4) * hm.m24 + (1/4) * hm.m25 + (-1/4) * hm.m26 + (-1/4) * hm.m34 + (-1/4) * hm.m35 + (1/4) * hm.m36

theorem consequence11 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : r0=1/6 := by
  linear_combination (1/6) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/6) * hm.m4 + (1/6) * hm.m5 + (-5/6) * hm.m6 + (-1/4) * hm.m14 + (-1/4) * hm.m15 + (1/2) * hm.m16 + (-1/4) * hm.m24 + (-1/4) * hm.m25 + (1/2) * hm.m26 + (-1/4) * hm.m34 + (-1/4) * hm.m35 + (1/2) * hm.m36 + (1/2) * hm.m45

theorem consequence12 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : r1=1/6 := by
  linear_combination (1/6) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/6) * hm.m4 + (-5/6) * hm.m5 + (1/6) * hm.m6 + (-1/4) * hm.m14 + (1/4) * hm.m15 + (-1/4) * hm.m24 + (1/4) * hm.m25 + (-1/4) * hm.m34 + (1/4) * hm.m35 + (1/2) * hm.m45

theorem consequence13 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : r2=1/6 := by
  linear_combination (1/6) * hm.n1 + (1/12) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (-5/6) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (1/4) * hm.m14 + (-1/4) * hm.m15 + (1/4) * hm.m24 + (-1/4) * hm.m25 + (1/4) * hm.m34 + (-1/4) * hm.m35 + (1/2) * hm.m45

theorem consequence14 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : r3=-r6/2 - r8/2 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (7/12) * hm.m1 + (-5/12) * hm.m2 + (-5/12) * hm.m3 + (1/6) * hm.m4 + (1/6) * hm.m5 + (1/6) * hm.m6 + (-1/4) * hm.m14 + (-1/4) * hm.m15 + (-1/2) * hm.m16 + (1/4) * hm.m24 + (1/4) * hm.m25 + (1/4) * hm.m34 + (1/4) * hm.m35 + (-1/2) * hm.m45

theorem consequence15 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : r4=-r6 - r8 + 1/3 := by
  linear_combination (1/3) * hm.n1 + (1/6) * hm.m1 + (1/6) * hm.m2 + (1/6) * hm.m3 + (1/3) * hm.m4 + (1/3) * hm.m5 + (1/3) * hm.m6 + (-1/2) * hm.m16 + (-1/2) * hm.m26 + (-1/2) * hm.m36 + -1 * hm.m45

theorem consequence16 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : r5=r6/2 := by
  linear_combination (-1/2) * hm.m1 + (1/2) * hm.m2 + (-1/2) * hm.m3 + (1/4) * hm.m14 + (1/4) * hm.m15 + (1/4) * hm.m16 + (-1/4) * hm.m24 + (-1/4) * hm.m25 + (-1/4) * hm.m26 + (1/4) * hm.m34 + (1/4) * hm.m35 + (1/4) * hm.m36

theorem consequence17 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : r6=r6 := by
  ring

theorem consequence18 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : r7=r8/2 := by
  linear_combination (-1/2) * hm.m1 + (-1/2) * hm.m2 + (1/2) * hm.m3 + (1/4) * hm.m14 + (1/4) * hm.m15 + (1/4) * hm.m16 + (1/4) * hm.m24 + (1/4) * hm.m25 + (1/4) * hm.m26 + (-1/4) * hm.m34 + (-1/4) * hm.m35 + (-1/4) * hm.m36

theorem consequence19 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8) : r8=r8 := by
  ring

theorem normal_coordinates (p : Fin 11 → ℝ) (q : Fin 9 → ℝ) (hm : Moment p q) :
    p=bottomProb (q ⟨6,by decide⟩) (q ⟨8,by decide⟩) ∧ q=topProb (q ⟨6,by decide⟩) (q ⟨8,by decide⟩) := by
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

theorem domain_of_moment (p : Fin 11 → ℝ) (q : Fin 9 → ℝ) (hm : Moment p q) : Domain (q ⟨6,by decide⟩) (q ⟨8,by decide⟩) := by
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
  refine ⟨?_ ,?_ ,?_⟩ <;>
    linarith only [hm.nq0,hm.nq1,hm.nq2,hm.nq3,hm.nq4,hm.nq5,hm.nq6,hm.nq7,hm.nq8,hm.nq9,hm.nq10,hm.nr0,hm.nr1,hm.nr2,hm.nr3,hm.nr4,hm.nr5,hm.nr6,hm.nr7,hm.nr8,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19]

theorem reconstruct (a b : ℝ) (h : Domain a b) :
    Moment (bottomProb a b) (topProb a b) := by
  obtain ⟨h0,h1,h2⟩ := h
  change MomentSystem (bottomProb a b ⟨0,by decide⟩) (bottomProb a b ⟨1,by decide⟩) (bottomProb a b ⟨2,by decide⟩) (bottomProb a b ⟨3,by decide⟩) (bottomProb a b ⟨4,by decide⟩) (bottomProb a b ⟨5,by decide⟩) (bottomProb a b ⟨6,by decide⟩) (bottomProb a b ⟨7,by decide⟩) (bottomProb a b ⟨8,by decide⟩) (bottomProb a b ⟨9,by decide⟩) (bottomProb a b ⟨10,by decide⟩) (topProb a b ⟨0,by decide⟩) (topProb a b ⟨1,by decide⟩) (topProb a b ⟨2,by decide⟩) (topProb a b ⟨3,by decide⟩) (topProb a b ⟨4,by decide⟩) (topProb a b ⟨5,by decide⟩) (topProb a b ⟨6,by decide⟩) (topProb a b ⟨7,by decide⟩) (topProb a b ⟨8,by decide⟩)
  constructor <;> norm_num [bottomProb,topProb] <;> linarith only [h0,h1,h2]

theorem complete_iff (p : Fin 11 → ℝ) (q : Fin 9 → ℝ) :
    Moment p q ↔ ∃ a b : ℝ, Domain a b ∧ p=bottomProb a b ∧ q=topProb a b := by
  constructor
  · intro hm
    exact ⟨(q ⟨6,by decide⟩),(q ⟨8,by decide⟩),domain_of_moment p q hm,normal_coordinates p q hm⟩
  · rintro ⟨a,b,hd,hp,hq⟩
    rw [hp,hq]
    exact reconstruct a b hd

theorem physical_normal_form (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∃ a b : ℝ, Domain a b ∧
      (fun i => Complex.normSq (c (bottom i)))=bottomProb a b ∧
      (fun i => Complex.normSq (d (top i)))=topProb a b := by
  apply (complete_iff _ _).1
  exact moments c d hc hd hnc hnd hkl
end Orbit48

namespace Orbit49
open SixQubit.Orbit49
def bottom : Fin 10 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9]
def top : Fin 10 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9]
def bottomProb (a b g : ℝ) : Fin 10 → ℝ := ![g,1/6 - g,b,1/6 - b,a,1/6 - a,-a - b - g + 1/3,a + b + g - 1/6,1/6,1/6]
def topProb (a b g : ℝ) : Fin 10 → ℝ := ![g,1/6 - g,b,1/6 - b,a,1/6 - a,-a - b - g + 1/3,a + b + g - 1/6,1/6,1/6]
def Domain (a b g : ℝ) : Prop := 0≤(a) ∧ 0≤(b) ∧ 0≤(g) ∧ 0≤(1/6 - a) ∧ 0≤(1/6 - b) ∧ 0≤(1/6 - g) ∧ 0≤(a + b + g - 1/6) ∧ 0≤(-a - b - g + 1/3)
def Moment (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) := MomentSystem (p ⟨0,by decide⟩) (p ⟨1,by decide⟩) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨4,by decide⟩) (p ⟨5,by decide⟩) (p ⟨6,by decide⟩) (p ⟨7,by decide⟩) (p ⟨8,by decide⟩) (p ⟨9,by decide⟩) (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩)
theorem actual_words :
    (∀ i, bottom i=MainTheory.OrderEightSupportDisplays.bits (![0,6,9,15,17,23,33,39,58,60] i)) ∧
    (∀ i, top i=MainTheory.OrderEightSupportDisplays.bits (![63,57,54,48,46,40,30,24,5,3] i)) ∧
    S0=Finset.univ.image bottom ∧ S1=Finset.univ.image top := by decide +kernel

def complementIndex : Fin 10 → Fin 10 := ![0,1,2,3,4,5,6,7,8,9]
theorem actual_complements : ∀ i, top (complementIndex i)=SS.complement (bottom i) := by decide +kernel

theorem consequence0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q0=q0 := by
  ring

theorem consequence1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q1=1/6 - q0 := by
  linear_combination 1 * hm.n0 + (-5/6) * hm.n1 + (-7/6) * hm.m1 + (-1/6) * hm.m2 + (-1/6) * hm.m3 + (-5/6) * hm.m6 + (1/2) * hm.m12 + (1/2) * hm.m13 + 1 * hm.m16 + (-1/2) * hm.m23

theorem consequence2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q2=q2 := by
  ring

theorem consequence3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q3=1/6 - q2 := by
  linear_combination (1/6) * hm.n1 + (-1/6) * hm.m1 + (-1/6) * hm.m2 + (5/6) * hm.m3 + (1/6) * hm.m6 + (1/2) * hm.m12 + (-1/2) * hm.m13 + (-1/2) * hm.m23

theorem consequence4 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q4=q4 := by
  ring

theorem consequence5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q5=1/6 - q4 := by
  linear_combination (1/6) * hm.n1 + (-1/6) * hm.m1 + (5/6) * hm.m2 + (-1/6) * hm.m3 + (1/6) * hm.m6 + (-1/2) * hm.m12 + (1/2) * hm.m13 + (-1/2) * hm.m23

theorem consequence6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q6=-q0 - q2 - q4 + 1/3 := by
  linear_combination 1 * hm.n0 + (-2/3) * hm.n1 + (-7/12) * hm.m1 + (-1/12) * hm.m2 + (-1/12) * hm.m3 + (-1/4) * hm.m4 + (-3/4) * hm.m5 + (1/12) * hm.m6 + (-1/2) * hm.m14 + 1 * hm.m15 + (1/2) * hm.m16 + (-1/2) * hm.m23 + (1/2) * hm.m24 + (1/2) * hm.m34 + (-1/2) * hm.m46

theorem consequence7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q7=q0 + q2 + q4 - 1/6 := by
  linear_combination -1 * hm.n0 + (5/6) * hm.n1 + (17/12) * hm.m1 + (-1/12) * hm.m2 + (-1/12) * hm.m3 + (1/4) * hm.m4 + (3/4) * hm.m5 + (1/12) * hm.m6 + (-1/2) * hm.m12 + (-1/2) * hm.m13 + (1/2) * hm.m14 + -1 * hm.m15 + (-1/2) * hm.m16 + 1 * hm.m23 + (-1/2) * hm.m24 + (-1/2) * hm.m34 + (1/2) * hm.m46

theorem consequence8 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q8=1/6 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (-1/6) * hm.m2 + (-1/6) * hm.m3 + (1/6) * hm.m6 + (-1/2) * hm.m14 + (1/2) * hm.m15 + (-1/2) * hm.m16 + (1/2) * hm.m23

theorem consequence9 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q9=1/6 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (-1/6) * hm.m2 + (-1/6) * hm.m3 + (1/6) * hm.m6 + (1/2) * hm.m14 + (-1/2) * hm.m15 + (-1/2) * hm.m16 + (1/2) * hm.m23

theorem consequence10 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r0=q0 := by
  linear_combination -1 * hm.n0 + 1 * hm.n1 + (5/4) * hm.m1 + (1/4) * hm.m2 + (1/4) * hm.m3 + (3/4) * hm.m4 + (1/4) * hm.m5 + (3/4) * hm.m6 + (-1/2) * hm.m12 + (-1/2) * hm.m13 + (-1/2) * hm.m15 + -1 * hm.m16 + (1/2) * hm.m23 + (-1/2) * hm.m24 + (-1/2) * hm.m34 + (-1/2) * hm.m46

theorem consequence11 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r1=1/6 - q0 := by
  linear_combination 1 * hm.n0 + (-5/6) * hm.n1 + (-5/12) * hm.m1 + (-5/12) * hm.m2 + (-5/12) * hm.m3 + (-3/4) * hm.m4 + (-1/4) * hm.m5 + (-7/12) * hm.m6 + (1/2) * hm.m15 + (1/2) * hm.m24 + (1/2) * hm.m34 + (1/2) * hm.m46

theorem consequence12 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r2=q2 := by
  linear_combination (1/4) * hm.m1 + (1/4) * hm.m2 + (-3/4) * hm.m3 + (-1/4) * hm.m4 + (1/4) * hm.m5 + (-1/4) * hm.m6 + (-1/2) * hm.m12 + (1/2) * hm.m13 + (-1/2) * hm.m15 + (1/2) * hm.m23 + (-1/2) * hm.m24 + (1/2) * hm.m34 + (1/2) * hm.m46

theorem consequence13 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r3=1/6 - q2 := by
  linear_combination (1/6) * hm.n1 + (-5/12) * hm.m1 + (-5/12) * hm.m2 + (7/12) * hm.m3 + (1/4) * hm.m4 + (-1/4) * hm.m5 + (5/12) * hm.m6 + (1/2) * hm.m15 + (1/2) * hm.m24 + (-1/2) * hm.m34 + (-1/2) * hm.m46

theorem consequence14 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r4=q4 := by
  linear_combination (1/4) * hm.m1 + (-3/4) * hm.m2 + (1/4) * hm.m3 + (-1/4) * hm.m4 + (1/4) * hm.m5 + (-1/4) * hm.m6 + (1/2) * hm.m12 + (-1/2) * hm.m13 + (-1/2) * hm.m15 + (1/2) * hm.m23 + (1/2) * hm.m24 + (-1/2) * hm.m34 + (1/2) * hm.m46

theorem consequence15 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r5=1/6 - q4 := by
  linear_combination (1/6) * hm.n1 + (-5/12) * hm.m1 + (7/12) * hm.m2 + (-5/12) * hm.m3 + (1/4) * hm.m4 + (-1/4) * hm.m5 + (5/12) * hm.m6 + (1/2) * hm.m15 + (-1/2) * hm.m24 + (1/2) * hm.m34 + (-1/2) * hm.m46

theorem consequence16 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r6=-q0 - q2 - q4 + 1/3 := by
  linear_combination 1 * hm.n0 + (-2/3) * hm.n1 + (-4/3) * hm.m1 + (1/6) * hm.m2 + (1/6) * hm.m3 + (-1/2) * hm.m4 + (-1/2) * hm.m5 + (-1/6) * hm.m6 + (1/2) * hm.m12 + (1/2) * hm.m13 + (1/2) * hm.m14 + (1/2) * hm.m15 + (1/2) * hm.m16 + -1 * hm.m23

theorem consequence17 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r7=q0 + q2 + q4 - 1/6 := by
  linear_combination -1 * hm.n0 + (5/6) * hm.n1 + (7/6) * hm.m1 + (-1/3) * hm.m2 + (-1/3) * hm.m3 + (1/2) * hm.m4 + (1/2) * hm.m5 + (1/3) * hm.m6 + (-1/2) * hm.m14 + (-1/2) * hm.m15 + (-1/2) * hm.m16 + (1/2) * hm.m23

theorem consequence18 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r8=1/6 := by
  linear_combination (1/6) * hm.n1 + (-1/6) * hm.m1 + (1/3) * hm.m2 + (1/3) * hm.m3 + (-1/2) * hm.m4 + (1/2) * hm.m5 + (-1/3) * hm.m6 + (1/2) * hm.m14 + (-1/2) * hm.m15 + (1/2) * hm.m16 + (-1/2) * hm.m23

theorem consequence19 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r9=1/6 := by
  linear_combination (1/6) * hm.n1 + (-1/6) * hm.m1 + (1/3) * hm.m2 + (1/3) * hm.m3 + (1/2) * hm.m4 + (-1/2) * hm.m5 + (-1/3) * hm.m6 + (-1/2) * hm.m14 + (1/2) * hm.m15 + (1/2) * hm.m16 + (-1/2) * hm.m23

theorem normal_coordinates (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) (hm : Moment p q) :
    p=bottomProb (p ⟨4,by decide⟩) (p ⟨2,by decide⟩) (p ⟨0,by decide⟩) ∧ q=topProb (p ⟨4,by decide⟩) (p ⟨2,by decide⟩) (p ⟨0,by decide⟩) := by
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

theorem domain_of_moment (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) (hm : Moment p q) : Domain (p ⟨4,by decide⟩) (p ⟨2,by decide⟩) (p ⟨0,by decide⟩) := by
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
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_⟩ <;>
    linarith only [hm.nq0,hm.nq1,hm.nq2,hm.nq3,hm.nq4,hm.nq5,hm.nq6,hm.nq7,hm.nq8,hm.nq9,hm.nr0,hm.nr1,hm.nr2,hm.nr3,hm.nr4,hm.nr5,hm.nr6,hm.nr7,hm.nr8,hm.nr9,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19]

theorem reconstruct (a b g : ℝ) (h : Domain a b g) :
    Moment (bottomProb a b g) (topProb a b g) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := h
  change MomentSystem (bottomProb a b g ⟨0,by decide⟩) (bottomProb a b g ⟨1,by decide⟩) (bottomProb a b g ⟨2,by decide⟩) (bottomProb a b g ⟨3,by decide⟩) (bottomProb a b g ⟨4,by decide⟩) (bottomProb a b g ⟨5,by decide⟩) (bottomProb a b g ⟨6,by decide⟩) (bottomProb a b g ⟨7,by decide⟩) (bottomProb a b g ⟨8,by decide⟩) (bottomProb a b g ⟨9,by decide⟩) (topProb a b g ⟨0,by decide⟩) (topProb a b g ⟨1,by decide⟩) (topProb a b g ⟨2,by decide⟩) (topProb a b g ⟨3,by decide⟩) (topProb a b g ⟨4,by decide⟩) (topProb a b g ⟨5,by decide⟩) (topProb a b g ⟨6,by decide⟩) (topProb a b g ⟨7,by decide⟩) (topProb a b g ⟨8,by decide⟩) (topProb a b g ⟨9,by decide⟩)
  constructor <;> norm_num [bottomProb,topProb] <;> linarith only [h0,h1,h2,h3,h4,h5,h6,h7]

theorem complete_iff (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) :
    Moment p q ↔ ∃ a b g : ℝ, Domain a b g ∧ p=bottomProb a b g ∧ q=topProb a b g := by
  constructor
  · intro hm
    exact ⟨(p ⟨4,by decide⟩),(p ⟨2,by decide⟩),(p ⟨0,by decide⟩),domain_of_moment p q hm,normal_coordinates p q hm⟩
  · rintro ⟨a,b,g,hd,hp,hq⟩
    rw [hp,hq]
    exact reconstruct a b g hd

theorem key_masses (p q : Fin 10 → ℝ) (hm : Moment p q) :
    (∀ i : Fin 4, p ⟨2*i.val,by omega⟩+p ⟨2*i.val+1,by omega⟩=1/6) ∧
    p ⟨8,by decide⟩=1/6 ∧ p ⟨9,by decide⟩=1/6 := by
  obtain ⟨a,b,g,_hd,hp,_hq⟩ := (complete_iff p q).1 hm
  rw [hp]
  refine ⟨?_,?_,?_⟩
  · intro i
    fin_cases i <;> norm_num [bottomProb]
    ring
  · norm_num [bottomProb]
  · norm_num [bottomProb]

theorem physical_normal_form (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∃ a b g : ℝ, Domain a b g ∧
      (fun i => Complex.normSq (c (bottom i)))=bottomProb a b g ∧
      (fun i => Complex.normSq (d (top i)))=topProb a b g := by
  apply (complete_iff _ _).1
  exact moments c d hc hd hnc hnd hkl
end Orbit49

namespace Orbit50
open SixQubit.Orbit50
def bottom : Fin 11 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9,y10]
def top : Fin 11 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10]
def bottomProb (a b g t : ℝ) : Fin 11 → ℝ := ![1/6,a,b,g,-a - b - g + 1/3,-a - b + 1/3,t,b - t,-g - t + 1/6,a + g + t - 1/6,1/6]
def topProb (a b g t : ℝ) : Fin 11 → ℝ := ![1/6,a + g + t - 1/6,-g - t + 1/6,b - t,t,-a - b + 1/3,-a - b - g + 1/3,g,b,a,1/6]
def Domain (a b g t : ℝ) : Prop := 0≤(a) ∧ 0≤(b) ∧ 0≤(g) ∧ 0≤(t) ∧ 0≤(-a - b - g + 1/3) ∧ 0≤(b - t) ∧ 0≤(-g - t + 1/6) ∧ 0≤(a + g + t - 1/6)
def Moment (p : Fin 11 → ℝ) (q : Fin 11 → ℝ) := MomentSystem (p ⟨0,by decide⟩) (p ⟨1,by decide⟩) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨4,by decide⟩) (p ⟨5,by decide⟩) (p ⟨6,by decide⟩) (p ⟨7,by decide⟩) (p ⟨8,by decide⟩) (p ⟨9,by decide⟩) (p ⟨10,by decide⟩) (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩) (q ⟨10,by decide⟩)
theorem actual_words :
    (∀ i, bottom i=MainTheory.OrderEightSupportDisplays.bits (![0,15,23,25,26,39,41,42,49,50,60] i)) ∧
    (∀ i, top i=MainTheory.OrderEightSupportDisplays.bits (![3,13,14,21,22,24,37,38,40,48,63] i)) ∧
    S0=Finset.univ.image bottom ∧ S1=Finset.univ.image top := by decide +kernel

def complementIndex : Fin 11 → Fin 11 := ![10,9,8,7,6,5,4,3,2,1,0]
theorem actual_complements : ∀ i, top (complementIndex i)=SS.complement (bottom i) := by decide +kernel

theorem consequence0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : q0=1/6 := by
  linear_combination 1 * hm.n0 + (-5/6) * hm.n1 + (-2/3) * hm.m1 + (-5/12) * hm.m2 + (-5/12) * hm.m3 + (-1/4) * hm.m4 + (-2/3) * hm.m5 + (-1/6) * hm.m6 + (1/4) * hm.m12 + (1/4) * hm.m13 + (1/4) * hm.m14 + (1/4) * hm.m15 + (1/4) * hm.m25 + (1/4) * hm.m35 + (1/4) * hm.m45

theorem consequence1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : q1=q1 := by
  ring

theorem consequence2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : q2=q2 := by
  ring

theorem consequence3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : q3=q3 := by
  ring

theorem consequence4 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : q4=-q1 - q2 - q3 + 1/3 := by
  linear_combination (1/3) * hm.n1 + (2/3) * hm.m1 + (1/6) * hm.m2 + (1/6) * hm.m3 + (-1/2) * hm.m4 + (-1/3) * hm.m5 + (2/3) * hm.m6 + (-1/2) * hm.m12 + (-1/2) * hm.m13 + (1/2) * hm.m14 + (-1/2) * hm.m15 + -1 * hm.m16 + (1/2) * hm.m25 + (1/2) * hm.m35 + (1/2) * hm.m45

theorem consequence5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : q5=-q1 - q2 + 1/3 := by
  linear_combination (1/3) * hm.n1 + (1/6) * hm.m1 + (1/6) * hm.m2 + (1/6) * hm.m3 + (-1/2) * hm.m4 + (-4/3) * hm.m5 + (5/3) * hm.m6 + (1/2) * hm.m15 + -1 * hm.m16 + (1/2) * hm.m25 + -1 * hm.m26 + (1/2) * hm.m35 + -1 * hm.m36 + (3/2) * hm.m45

theorem consequence6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : q6=q6 := by
  ring

theorem consequence7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : q7=q2 - q6 := by
  linear_combination (1/2) * hm.m2 + (-1/2) * hm.m3 + (1/2) * hm.m4 + 1 * hm.m5 + -1 * hm.m6 + (-1/2) * hm.m12 + (1/2) * hm.m13 + (-1/2) * hm.m14 + 1 * hm.m16 + -1 * hm.m25 + 1 * hm.m36 + -1 * hm.m45

theorem consequence8 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : q8=-q3 - q6 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/4) * hm.m4 + (4/3) * hm.m5 + (-7/6) * hm.m6 + (-1/4) * hm.m12 + (-1/4) * hm.m13 + (-1/4) * hm.m14 + (-3/4) * hm.m15 + 1 * hm.m16 + (-3/4) * hm.m25 + 1 * hm.m26 + (-3/4) * hm.m35 + 1 * hm.m36 + (-3/4) * hm.m45

theorem consequence9 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : q9=q1 + q3 + q6 - 1/6 := by
  linear_combination (-1/6) * hm.n1 + (-1/3) * hm.m1 + (-7/12) * hm.m2 + (5/12) * hm.m3 + (1/4) * hm.m4 + (-1/3) * hm.m5 + (1/6) * hm.m6 + (3/4) * hm.m12 + (-1/4) * hm.m13 + (-1/4) * hm.m14 + (3/4) * hm.m15 + (3/4) * hm.m25 + (-1/4) * hm.m35 + -1 * hm.m36 + (-1/4) * hm.m45

theorem consequence10 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : q10=1/6 := by
  linear_combination (1/6) * hm.n1 + (-1/6) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/4) * hm.m4 + (1/3) * hm.m5 + (-1/6) * hm.m6 + (1/4) * hm.m12 + (1/4) * hm.m13 + (1/4) * hm.m14 + (-1/4) * hm.m15 + (-1/4) * hm.m25 + (-1/4) * hm.m35 + (-1/4) * hm.m45

theorem consequence11 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : r0=1/6 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/4) * hm.m4 + (-2/3) * hm.m5 + (-1/6) * hm.m6 + (-1/4) * hm.m12 + (-1/4) * hm.m13 + (-1/4) * hm.m14 + (1/4) * hm.m15 + (1/4) * hm.m25 + (1/4) * hm.m35 + (1/4) * hm.m45

theorem consequence12 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : r1=q1 + q3 + q6 - 1/6 := by
  linear_combination (-1/6) * hm.n1 + (-1/3) * hm.m1 + (-1/12) * hm.m2 + (-1/12) * hm.m3 + (-1/4) * hm.m4 + (-1/3) * hm.m5 + (1/6) * hm.m6 + (1/4) * hm.m12 + (1/4) * hm.m13 + (1/4) * hm.m14 + (1/4) * hm.m15 + (1/4) * hm.m25 + (1/4) * hm.m35 + -1 * hm.m36 + (1/4) * hm.m45

theorem consequence13 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : r2=-q3 - q6 + 1/6 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (7/12) * hm.m2 + (-5/12) * hm.m3 + (-1/4) * hm.m4 + (1/3) * hm.m5 + (-1/6) * hm.m6 + (-3/4) * hm.m12 + (1/4) * hm.m13 + (1/4) * hm.m14 + (-1/4) * hm.m15 + (-1/4) * hm.m25 + (-1/4) * hm.m35 + 1 * hm.m36 + (-1/4) * hm.m45

theorem consequence14 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : r3=q2 - q6 := by
  linear_combination 1 * hm.m5 + -1 * hm.m6 + (-1/2) * hm.m15 + 1 * hm.m16 + (-1/2) * hm.m25 + (-1/2) * hm.m35 + 1 * hm.m36 + (-1/2) * hm.m45

theorem consequence15 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : r4=q6 := by
  linear_combination (-1/2) * hm.m2 + (1/2) * hm.m3 + (-1/2) * hm.m4 + -1 * hm.m5 + 1 * hm.m6 + (1/2) * hm.m12 + (-1/2) * hm.m13 + (1/2) * hm.m14 + (1/2) * hm.m15 + -1 * hm.m16 + (1/2) * hm.m25 + (1/2) * hm.m35 + -1 * hm.m36 + (1/2) * hm.m45

theorem consequence16 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : r5=-q1 - q2 + 1/3 := by
  linear_combination (1/3) * hm.n1 + (2/3) * hm.m1 + (-1/3) * hm.m2 + (-1/3) * hm.m3 + (-1/3) * hm.m5 + (2/3) * hm.m6 + (-1/2) * hm.m15 + -1 * hm.m16 + (1/2) * hm.m25 + (1/2) * hm.m35 + (1/2) * hm.m45

theorem consequence17 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : r6=-q1 - q2 - q3 + 1/3 := by
  linear_combination (1/3) * hm.n1 + (1/6) * hm.m1 + (1/6) * hm.m2 + (1/6) * hm.m3 + (-1/2) * hm.m4 + (-1/3) * hm.m5 + (2/3) * hm.m6 + -1 * hm.m16 + 1 * hm.m45

theorem consequence18 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : r7=q3 := by
  linear_combination (-1/2) * hm.m1 + -1 * hm.m5 + 1 * hm.m6 + (1/2) * hm.m12 + (1/2) * hm.m13 + (-1/2) * hm.m14 + (1/2) * hm.m15 + (1/2) * hm.m25 + -1 * hm.m26 + (1/2) * hm.m35 + -1 * hm.m36 + (1/2) * hm.m45

theorem consequence19 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : r8=q2 := by
  linear_combination (-1/2) * hm.m1 + (1/2) * hm.m2 + (-1/2) * hm.m3 + (1/2) * hm.m4 + 1 * hm.m5 + -1 * hm.m6 + 1 * hm.m16 + -1 * hm.m25 + 1 * hm.m36 + -1 * hm.m45

theorem consequence20 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : r9=q1 := by
  linear_combination (-1/2) * hm.m1 + (-1/2) * hm.m2 + (1/2) * hm.m3 + (1/2) * hm.m4 + 1 * hm.m5 + -1 * hm.m6 + 1 * hm.m16 + 1 * hm.m26 + -1 * hm.m35 + -1 * hm.m45

theorem consequence21 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10) : r10=1/6 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (1/12) * hm.m2 + (1/12) * hm.m3 + (1/4) * hm.m4 + (1/3) * hm.m5 + (-1/6) * hm.m6 + (-1/4) * hm.m12 + (-1/4) * hm.m13 + (-1/4) * hm.m14 + (-1/4) * hm.m15 + (-1/4) * hm.m25 + (-1/4) * hm.m35 + (-1/4) * hm.m45

theorem normal_coordinates (p : Fin 11 → ℝ) (q : Fin 11 → ℝ) (hm : Moment p q) :
    p=bottomProb (p ⟨1,by decide⟩) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨6,by decide⟩) ∧ q=topProb (p ⟨1,by decide⟩) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨6,by decide⟩) := by
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
  have h20 := consequence20 hm
  have h21 := consequence21 hm
  constructor
  · ext i
    fin_cases i <;> norm_num [bottomProb,Fin.succ] at * <;> linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21]
  · ext i
    fin_cases i <;> norm_num [topProb,Fin.succ] at * <;> linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21]

theorem domain_of_moment (p : Fin 11 → ℝ) (q : Fin 11 → ℝ) (hm : Moment p q) : Domain (p ⟨1,by decide⟩) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨6,by decide⟩) := by
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
  have h20 := consequence20 hm
  have h21 := consequence21 hm
  unfold Domain
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_⟩ <;>
    linarith only [hm.nq0,hm.nq1,hm.nq2,hm.nq3,hm.nq4,hm.nq5,hm.nq6,hm.nq7,hm.nq8,hm.nq9,hm.nq10,hm.nr0,hm.nr1,hm.nr2,hm.nr3,hm.nr4,hm.nr5,hm.nr6,hm.nr7,hm.nr8,hm.nr9,hm.nr10,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21]

theorem reconstruct (a b g t : ℝ) (h : Domain a b g t) :
    Moment (bottomProb a b g t) (topProb a b g t) := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7⟩ := h
  change MomentSystem (bottomProb a b g t ⟨0,by decide⟩) (bottomProb a b g t ⟨1,by decide⟩) (bottomProb a b g t ⟨2,by decide⟩) (bottomProb a b g t ⟨3,by decide⟩) (bottomProb a b g t ⟨4,by decide⟩) (bottomProb a b g t ⟨5,by decide⟩) (bottomProb a b g t ⟨6,by decide⟩) (bottomProb a b g t ⟨7,by decide⟩) (bottomProb a b g t ⟨8,by decide⟩) (bottomProb a b g t ⟨9,by decide⟩) (bottomProb a b g t ⟨10,by decide⟩) (topProb a b g t ⟨0,by decide⟩) (topProb a b g t ⟨1,by decide⟩) (topProb a b g t ⟨2,by decide⟩) (topProb a b g t ⟨3,by decide⟩) (topProb a b g t ⟨4,by decide⟩) (topProb a b g t ⟨5,by decide⟩) (topProb a b g t ⟨6,by decide⟩) (topProb a b g t ⟨7,by decide⟩) (topProb a b g t ⟨8,by decide⟩) (topProb a b g t ⟨9,by decide⟩) (topProb a b g t ⟨10,by decide⟩)
  constructor <;> norm_num [bottomProb,topProb] <;> linarith only [h0,h1,h2,h3,h4,h5,h6,h7]

theorem complete_iff (p : Fin 11 → ℝ) (q : Fin 11 → ℝ) :
    Moment p q ↔ ∃ a b g t : ℝ, Domain a b g t ∧ p=bottomProb a b g t ∧ q=topProb a b g t := by
  constructor
  · intro hm
    exact ⟨(p ⟨1,by decide⟩),(p ⟨2,by decide⟩),(p ⟨3,by decide⟩),(p ⟨6,by decide⟩),domain_of_moment p q hm,normal_coordinates p q hm⟩
  · rintro ⟨a,b,g,t,hd,hp,hq⟩
    rw [hp,hq]
    exact reconstruct a b g t hd

theorem key_masses (p q : Fin 11 → ℝ) (hm : Moment p q) :
    p ⟨0,by decide⟩=1/6 ∧ p ⟨10,by decide⟩=1/6 ∧
    p ⟨1,by decide⟩+p ⟨2,by decide⟩+p ⟨5,by decide⟩=1/3 := by
  obtain ⟨a,b,g,t,_hd,hp,_hq⟩ := (complete_iff p q).1 hm
  rw [hp]
  refine ⟨?_,?_,?_⟩ <;> norm_num [bottomProb]
  ring

theorem physical_normal_form (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∃ a b g t : ℝ, Domain a b g t ∧
      (fun i => Complex.normSq (c (bottom i)))=bottomProb a b g t ∧
      (fun i => Complex.normSq (d (top i)))=topProb a b g t := by
  apply (complete_iff _ _).1
  exact moments c d hc hd hnc hnd hkl
end Orbit50

namespace Orbit51
open SixQubit.Orbit51
def bottom : Fin 10 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9]
def top : Fin 10 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9]
def bottomProb (a b g : ℝ) : Fin 10 → ℝ := ![g,1/6 - g,b,1/6 - b,a,1/6 - a,1/6 - a,a,-b - g + 1/3,b + g]
def topProb (a b g : ℝ) : Fin 10 → ℝ := ![g,1/6 - g,b,1/6 - b,a,1/6 - a,1/6 - a,a,-b - g + 1/3,b + g]
def Domain (a b g : ℝ) : Prop := 0≤(a) ∧ 0≤(b) ∧ 0≤(g) ∧ 0≤(1/6 - a) ∧ 0≤(1/6 - b) ∧ 0≤(1/6 - g)
def Moment (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) := MomentSystem (p ⟨0,by decide⟩) (p ⟨1,by decide⟩) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨4,by decide⟩) (p ⟨5,by decide⟩) (p ⟨6,by decide⟩) (p ⟨7,by decide⟩) (p ⟨8,by decide⟩) (p ⟨9,by decide⟩) (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩)
theorem actual_words :
    (∀ i, bottom i=MainTheory.OrderEightSupportDisplays.bits (![0,6,9,15,26,28,42,44,49,55] i)) ∧
    (∀ i, top i=MainTheory.OrderEightSupportDisplays.bits (![63,57,54,48,37,35,21,19,14,8] i)) ∧
    S0=Finset.univ.image bottom ∧ S1=Finset.univ.image top := by decide +kernel

def complementIndex : Fin 10 → Fin 10 := ![0,1,2,3,4,5,6,7,8,9]
theorem actual_complements : ∀ i, top (complementIndex i)=SS.complement (bottom i) := by decide +kernel

theorem consequence0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q0=q0 := by
  ring

theorem consequence1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q1=1/6 - q0 := by
  linear_combination 1 * hm.n0 + (-5/6) * hm.n1 + (-2/3) * hm.m1 + (-2/3) * hm.m2 + (-5/6) * hm.m3 + (-1/6) * hm.m6 + (1/2) * hm.m12 + (1/2) * hm.m13 + (1/2) * hm.m23

theorem consequence2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q2=q2 := by
  ring

theorem consequence3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q3=1/6 - q2 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (-2/3) * hm.m2 + (1/6) * hm.m3 + (5/6) * hm.m6 + (1/2) * hm.m12 + (-1/2) * hm.m13 + -1 * hm.m16 + (1/2) * hm.m23

theorem consequence4 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q4=q4 := by
  ring

theorem consequence5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q5=1/6 - q4 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (1/3) * hm.m2 + (1/6) * hm.m3 + (-1/6) * hm.m6 + (-1/2) * hm.m12 + (-1/2) * hm.m13 + (1/2) * hm.m23

theorem consequence6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q6=1/6 - q4 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (1/3) * hm.m2 + (1/6) * hm.m3 + (-1/6) * hm.m6 + (-1/2) * hm.m12 + (-1/2) * hm.m34 + (1/2) * hm.m35

theorem consequence7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q7=q4 := by
  linear_combination (1/2) * hm.m13 + (-1/2) * hm.m23 + (1/2) * hm.m34 + (-1/2) * hm.m35

theorem consequence8 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q8=-q0 - q2 + 1/3 := by
  linear_combination 1 * hm.n0 + (-2/3) * hm.n1 + (-5/6) * hm.m1 + (-1/3) * hm.m2 + (-2/3) * hm.m3 + -1 * hm.m5 + (2/3) * hm.m6 + (1/2) * hm.m12 + (1/2) * hm.m14 + (1/2) * hm.m15 + 1 * hm.m35 + -1 * hm.m46

theorem consequence9 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q9=q0 + q2 := by
  linear_combination -1 * hm.n0 + 1 * hm.n1 + (1/2) * hm.m1 + 1 * hm.m2 + 1 * hm.m3 + 1 * hm.m5 + -1 * hm.m6 + (-1/2) * hm.m12 + (-1/2) * hm.m14 + (-1/2) * hm.m15 + 1 * hm.m16 + -1 * hm.m23 + -1 * hm.m35 + 1 * hm.m46

theorem consequence10 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r0=q0 := by
  linear_combination -1 * hm.n0 + 1 * hm.n1 + 1 * hm.m1 + (1/2) * hm.m2 + 1 * hm.m3 + (1/2) * hm.m4 + (1/2) * hm.m5 + (-1/2) * hm.m12 + (-1/2) * hm.m13 + (-1/2) * hm.m14 + (-1/2) * hm.m15 + (-1/2) * hm.m23 + (-1/2) * hm.m34 + (-1/2) * hm.m35

theorem consequence11 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r1=1/6 - q0 := by
  linear_combination 1 * hm.n0 + (-5/6) * hm.n1 + (-2/3) * hm.m1 + (-1/6) * hm.m2 + (-5/6) * hm.m3 + (-1/2) * hm.m4 + (-1/2) * hm.m5 + (-1/6) * hm.m6 + (1/2) * hm.m14 + (1/2) * hm.m15 + (1/2) * hm.m34 + (1/2) * hm.m35

theorem consequence12 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r2=q2 := by
  linear_combination (1/2) * hm.m2 + (-1/2) * hm.m4 + (1/2) * hm.m5 + -1 * hm.m6 + (-1/2) * hm.m12 + (1/2) * hm.m13 + (-1/2) * hm.m14 + (-1/2) * hm.m15 + 1 * hm.m16 + (-1/2) * hm.m23 + (1/2) * hm.m34 + (-1/2) * hm.m35 + 1 * hm.m46

theorem consequence13 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r3=1/6 - q2 := by
  linear_combination (1/6) * hm.n1 + (-2/3) * hm.m1 + (-1/6) * hm.m2 + (1/6) * hm.m3 + (1/2) * hm.m4 + (-1/2) * hm.m5 + (5/6) * hm.m6 + (1/2) * hm.m14 + (1/2) * hm.m15 + (-1/2) * hm.m34 + (1/2) * hm.m35 + -1 * hm.m46

theorem consequence14 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r4=q4 := by
  linear_combination (-1/2) * hm.m1 + (1/2) * hm.m12 + (1/2) * hm.m13 + (-1/2) * hm.m14 + (1/2) * hm.m15 + (-1/2) * hm.m23 + (1/2) * hm.m34 + (-1/2) * hm.m35

theorem consequence15 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r5=1/6 - q4 := by
  linear_combination (1/6) * hm.n1 + (-1/6) * hm.m1 + (1/3) * hm.m2 + (1/6) * hm.m3 + (-1/6) * hm.m6 + (1/2) * hm.m14 + (-1/2) * hm.m15 + (-1/2) * hm.m34 + (1/2) * hm.m35

theorem consequence16 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r6=1/6 - q4 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (-1/6) * hm.m2 + (1/6) * hm.m3 + (-1/2) * hm.m4 + (1/2) * hm.m5 + (-1/6) * hm.m6 + (-1/2) * hm.m13 + (1/2) * hm.m14 + (-1/2) * hm.m15 + (1/2) * hm.m23

theorem consequence17 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r7=q4 := by
  linear_combination (-1/2) * hm.m2 + (1/2) * hm.m4 + (-1/2) * hm.m5 + (1/2) * hm.m12 + (-1/2) * hm.m14 + (1/2) * hm.m15

theorem consequence18 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r8=-q0 - q2 + 1/3 := by
  linear_combination 1 * hm.n0 + (-2/3) * hm.n1 + (-1/3) * hm.m1 + (-5/6) * hm.m2 + (-2/3) * hm.m3 + (-1/2) * hm.m4 + (-1/2) * hm.m5 + (2/3) * hm.m6 + (1/2) * hm.m12 + (1/2) * hm.m14 + (1/2) * hm.m15 + -1 * hm.m16 + 1 * hm.m23

theorem consequence19 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r9=q0 + q2 := by
  linear_combination -1 * hm.n0 + 1 * hm.n1 + 1 * hm.m1 + (1/2) * hm.m2 + (1/2) * hm.m4 + (1/2) * hm.m5 + (-1/2) * hm.m12 + (-1/2) * hm.m14 + (-1/2) * hm.m15

theorem normal_coordinates (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) (hm : Moment p q) :
    p=bottomProb (p ⟨4,by decide⟩) (p ⟨2,by decide⟩) (p ⟨0,by decide⟩) ∧ q=topProb (p ⟨4,by decide⟩) (p ⟨2,by decide⟩) (p ⟨0,by decide⟩) := by
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

theorem domain_of_moment (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) (hm : Moment p q) : Domain (p ⟨4,by decide⟩) (p ⟨2,by decide⟩) (p ⟨0,by decide⟩) := by
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
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_⟩ <;>
    linarith only [hm.nq0,hm.nq1,hm.nq2,hm.nq3,hm.nq4,hm.nq5,hm.nq6,hm.nq7,hm.nq8,hm.nq9,hm.nr0,hm.nr1,hm.nr2,hm.nr3,hm.nr4,hm.nr5,hm.nr6,hm.nr7,hm.nr8,hm.nr9,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19]

theorem reconstruct (a b g : ℝ) (h : Domain a b g) :
    Moment (bottomProb a b g) (topProb a b g) := by
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := h
  change MomentSystem (bottomProb a b g ⟨0,by decide⟩) (bottomProb a b g ⟨1,by decide⟩) (bottomProb a b g ⟨2,by decide⟩) (bottomProb a b g ⟨3,by decide⟩) (bottomProb a b g ⟨4,by decide⟩) (bottomProb a b g ⟨5,by decide⟩) (bottomProb a b g ⟨6,by decide⟩) (bottomProb a b g ⟨7,by decide⟩) (bottomProb a b g ⟨8,by decide⟩) (bottomProb a b g ⟨9,by decide⟩) (topProb a b g ⟨0,by decide⟩) (topProb a b g ⟨1,by decide⟩) (topProb a b g ⟨2,by decide⟩) (topProb a b g ⟨3,by decide⟩) (topProb a b g ⟨4,by decide⟩) (topProb a b g ⟨5,by decide⟩) (topProb a b g ⟨6,by decide⟩) (topProb a b g ⟨7,by decide⟩) (topProb a b g ⟨8,by decide⟩) (topProb a b g ⟨9,by decide⟩)
  constructor <;> norm_num [bottomProb,topProb] <;> linarith only [h0,h1,h2,h3,h4,h5]

theorem complete_iff (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) :
    Moment p q ↔ ∃ a b g : ℝ, Domain a b g ∧ p=bottomProb a b g ∧ q=topProb a b g := by
  constructor
  · intro hm
    exact ⟨(p ⟨4,by decide⟩),(p ⟨2,by decide⟩),(p ⟨0,by decide⟩),domain_of_moment p q hm,normal_coordinates p q hm⟩
  · rintro ⟨a,b,g,hd,hp,hq⟩
    rw [hp,hq]
    exact reconstruct a b g hd

theorem physical_normal_form (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∃ a b g : ℝ, Domain a b g ∧
      (fun i => Complex.normSq (c (bottom i)))=bottomProb a b g ∧
      (fun i => Complex.normSq (d (top i)))=topProb a b g := by
  apply (complete_iff _ _).1
  exact moments c d hc hd hnc hnd hkl
end Orbit51

namespace Orbit52
open SixQubit.Orbit52
def bottom : Fin 10 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6,y7,y8,y9]
def top : Fin 10 → SS.BitString 6 := ![z0,z1,z2,z3,z4,z5,z6,z7,z8,z9]
def bottomProb (a b : ℝ) : Fin 10 → ℝ := ![1/6 - a/2,a/2,1/6 - a/2,1/6 - a/2,a/2,a/2,1/3 - 2*b,2*b,1/6 - b,b]
def topProb (a b : ℝ) : Fin 10 → ℝ := ![1/6 - a/2,a/2,1/3 - a,a,1/6 - b,1/6 - b,b,b,1/6 - b,b]
def Domain (a b : ℝ) : Prop := 0≤(a) ∧ 0≤(b) ∧ 0≤(1/3 - a) ∧ 0≤(1/6 - b)
def Moment (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) := MomentSystem (p ⟨0,by decide⟩) (p ⟨1,by decide⟩) (p ⟨2,by decide⟩) (p ⟨3,by decide⟩) (p ⟨4,by decide⟩) (p ⟨5,by decide⟩) (p ⟨6,by decide⟩) (p ⟨7,by decide⟩) (p ⟨8,by decide⟩) (p ⟨9,by decide⟩) (q ⟨0,by decide⟩) (q ⟨1,by decide⟩) (q ⟨2,by decide⟩) (q ⟨3,by decide⟩) (q ⟨4,by decide⟩) (q ⟨5,by decide⟩) (q ⟨6,by decide⟩) (q ⟨7,by decide⟩) (q ⟨8,by decide⟩) (q ⟨9,by decide⟩)
theorem actual_words :
    (∀ i, bottom i=MainTheory.OrderEightSupportDisplays.bits (![0,12,17,18,29,30,39,43,52,56] i)) ∧
    (∀ i, top i=MainTheory.OrderEightSupportDisplays.bits (![3,15,16,28,37,38,41,42,55,59] i)) ∧
    S0=Finset.univ.image bottom ∧ S1=Finset.univ.image top := by decide +kernel

theorem consequence0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q0=1/6 - r3/2 := by
  linear_combination 1 * hm.n0 + (-5/6) * hm.n1 + (-1/6) * hm.m1 + (-5/6) * hm.m2 + (-1/2) * hm.m3 + (-1/2) * hm.m4 + (-2/3) * hm.m5 + (-1/6) * hm.m6 + (1/4) * hm.m12 + (1/4) * hm.m15 + (-1/4) * hm.m16 + (1/4) * hm.m23 + (1/4) * hm.m24 + (1/2) * hm.m25 + (1/4) * hm.m35 + (1/4) * hm.m36 + (1/4) * hm.m45 + (1/4) * hm.m46

theorem consequence1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q1=r3/2 := by
  linear_combination (-1/2) * hm.m1 + (1/2) * hm.m3 + (1/2) * hm.m4 + (1/4) * hm.m12 + (1/4) * hm.m15 + (1/4) * hm.m16 + (-1/4) * hm.m23 + (-1/4) * hm.m24 + (-1/4) * hm.m35 + (-1/4) * hm.m36 + (-1/4) * hm.m45 + (-1/4) * hm.m46

theorem consequence2 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q2=1/6 - r3/2 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (1/6) * hm.m2 + (-2/3) * hm.m5 + (5/6) * hm.m6 + (-1/4) * hm.m12 + (1/4) * hm.m15 + (-3/4) * hm.m16 + (-1/4) * hm.m23 + (-1/4) * hm.m24 + (1/2) * hm.m25 + (1/4) * hm.m35 + (-1/4) * hm.m36 + (1/4) * hm.m45 + (-1/4) * hm.m46

theorem consequence3 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q3=1/6 - r3/2 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (1/6) * hm.m2 + (1/3) * hm.m5 + (-1/6) * hm.m6 + (-1/4) * hm.m12 + (-1/4) * hm.m15 + (-1/4) * hm.m16 + (-1/4) * hm.m23 + (-1/4) * hm.m24 + (1/2) * hm.m25 + (-1/4) * hm.m35 + (1/4) * hm.m36 + (-1/4) * hm.m45 + (1/4) * hm.m46

theorem consequence4 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q4=r3/2 := by
  linear_combination (-1/4) * hm.m12 + (1/4) * hm.m15 + (-1/4) * hm.m16 + (1/4) * hm.m23 + (1/4) * hm.m24 + (-1/4) * hm.m35 + (1/4) * hm.m36 + (-1/4) * hm.m45 + (1/4) * hm.m46

theorem consequence5 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q5=r3/2 := by
  linear_combination (-1/4) * hm.m12 + (-1/4) * hm.m15 + (1/4) * hm.m16 + (1/4) * hm.m23 + (1/4) * hm.m24 + (1/4) * hm.m35 + (-1/4) * hm.m36 + (1/4) * hm.m45 + (-1/4) * hm.m46

theorem consequence6 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q6=1/3 - 2*q9 := by
  linear_combination (1/3) * hm.n1 + (1/6) * hm.m1 + (1/3) * hm.m2 + (1/2) * hm.m3 + (-1/2) * hm.m4 + (2/3) * hm.m5 + (-1/3) * hm.m6 + (1/2) * hm.m12 + (-1/2) * hm.m15 + (1/2) * hm.m16 + (1/2) * hm.m23 + (-1/2) * hm.m24 + -1 * hm.m25 + (-1/2) * hm.m35 + (-1/2) * hm.m36 + (1/2) * hm.m45 + (1/2) * hm.m46

theorem consequence7 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q7=2*q9 := by
  linear_combination (-1/2) * hm.m1 + (-1/2) * hm.m3 + (1/2) * hm.m4 + (-1/2) * hm.m12 + (1/2) * hm.m15 + (1/2) * hm.m16 + (-1/2) * hm.m23 + (1/2) * hm.m24 + (1/2) * hm.m35 + (1/2) * hm.m36 + (-1/2) * hm.m45 + (-1/2) * hm.m46

theorem consequence8 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q8=1/6 - q9 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (1/6) * hm.m2 + (1/3) * hm.m5 + (-1/6) * hm.m6 + (1/2) * hm.m12 + (-1/2) * hm.m15 + (-1/2) * hm.m25

theorem consequence9 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : q9=q9 := by
  ring

theorem consequence10 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r0=1/6 - r3/2 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (1/6) * hm.m2 + (-2/3) * hm.m5 + (-1/6) * hm.m6 + (-1/4) * hm.m12 + (1/4) * hm.m15 + (-1/4) * hm.m16 + (-1/4) * hm.m23 + (-1/4) * hm.m24 + (1/2) * hm.m25 + (1/4) * hm.m35 + (1/4) * hm.m36 + (1/4) * hm.m45 + (1/4) * hm.m46

theorem consequence11 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r1=r3/2 := by
  linear_combination (-1/4) * hm.m12 + (1/4) * hm.m15 + (1/4) * hm.m16 + (1/4) * hm.m23 + (1/4) * hm.m24 + (-1/4) * hm.m35 + (-1/4) * hm.m36 + (-1/4) * hm.m45 + (-1/4) * hm.m46

theorem consequence12 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r2=1/3 - r3 := by
  linear_combination (1/3) * hm.n1 + (2/3) * hm.m1 + (-2/3) * hm.m2 + (-1/3) * hm.m5 + (2/3) * hm.m6 + -1 * hm.m16 + 1 * hm.m25

theorem consequence13 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (_hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r3=r3 := by
  ring

theorem consequence14 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r4=1/6 - q9 := by
  linear_combination (1/6) * hm.n1 + (-1/6) * hm.m1 + (1/6) * hm.m2 + (1/2) * hm.m3 + (-1/2) * hm.m4 + (1/3) * hm.m5 + (-1/6) * hm.m6 + (1/2) * hm.m12 + (-1/2) * hm.m25 + (-1/2) * hm.m35 + (1/2) * hm.m45

theorem consequence15 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r5=1/6 - q9 := by
  linear_combination (1/6) * hm.n1 + (-1/6) * hm.m1 + (1/6) * hm.m2 + (1/2) * hm.m3 + (-1/2) * hm.m4 + (1/3) * hm.m5 + (-1/6) * hm.m6 + (1/2) * hm.m12 + (-1/2) * hm.m15 + (1/2) * hm.m16 + (-1/2) * hm.m25 + (-1/2) * hm.m36 + (1/2) * hm.m46

theorem consequence16 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r6=q9 := by
  linear_combination (-1/2) * hm.m1 + (-1/2) * hm.m3 + (1/2) * hm.m4 + (1/2) * hm.m15 + (1/2) * hm.m35 + (-1/2) * hm.m45

theorem consequence17 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r7=q9 := by
  linear_combination (-1/2) * hm.m1 + (-1/2) * hm.m3 + (1/2) * hm.m4 + (1/2) * hm.m16 + (1/2) * hm.m36 + (-1/2) * hm.m46

theorem consequence18 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r8=1/6 - q9 := by
  linear_combination (1/6) * hm.n1 + (1/3) * hm.m1 + (1/6) * hm.m2 + (1/3) * hm.m5 + (-1/6) * hm.m6 + (-1/2) * hm.m15 + (1/2) * hm.m23 + (-1/2) * hm.m24 + (-1/2) * hm.m25

theorem consequence19 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9) : r9=q9 := by
  linear_combination (-1/2) * hm.m12 + (-1/2) * hm.m23 + (1/2) * hm.m24

theorem normal_coordinates (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) (hm : Moment p q) :
    p=bottomProb (q ⟨3,by decide⟩) (p ⟨9,by decide⟩) ∧ q=topProb (q ⟨3,by decide⟩) (p ⟨9,by decide⟩) := by
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

theorem domain_of_moment (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) (hm : Moment p q) : Domain (q ⟨3,by decide⟩) (p ⟨9,by decide⟩) := by
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

theorem reconstruct (a b : ℝ) (h : Domain a b) :
    Moment (bottomProb a b) (topProb a b) := by
  obtain ⟨h0,h1,h2,h3⟩ := h
  change MomentSystem (bottomProb a b ⟨0,by decide⟩) (bottomProb a b ⟨1,by decide⟩) (bottomProb a b ⟨2,by decide⟩) (bottomProb a b ⟨3,by decide⟩) (bottomProb a b ⟨4,by decide⟩) (bottomProb a b ⟨5,by decide⟩) (bottomProb a b ⟨6,by decide⟩) (bottomProb a b ⟨7,by decide⟩) (bottomProb a b ⟨8,by decide⟩) (bottomProb a b ⟨9,by decide⟩) (topProb a b ⟨0,by decide⟩) (topProb a b ⟨1,by decide⟩) (topProb a b ⟨2,by decide⟩) (topProb a b ⟨3,by decide⟩) (topProb a b ⟨4,by decide⟩) (topProb a b ⟨5,by decide⟩) (topProb a b ⟨6,by decide⟩) (topProb a b ⟨7,by decide⟩) (topProb a b ⟨8,by decide⟩) (topProb a b ⟨9,by decide⟩)
  constructor <;> norm_num [bottomProb,topProb] <;> linarith only [h0,h1,h2,h3]

theorem complete_iff (p : Fin 10 → ℝ) (q : Fin 10 → ℝ) :
    Moment p q ↔ ∃ a b : ℝ, Domain a b ∧ p=bottomProb a b ∧ q=topProb a b := by
  constructor
  · intro hm
    exact ⟨(q ⟨3,by decide⟩),(p ⟨9,by decide⟩),domain_of_moment p q hm,normal_coordinates p q hm⟩
  · rintro ⟨a,b,hd,hp,hq⟩
    rw [hp,hq]
    exact reconstruct a b hd

theorem physical_normal_form (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∃ a b : ℝ, Domain a b ∧
      (fun i => Complex.normSq (c (bottom i)))=bottomProb a b ∧
      (fun i => Complex.normSq (d (top i)))=topProb a b := by
  apply (complete_iff _ _).1
  exact moments c d hc hd hnc hnd hkl
end Orbit52

end
end MainTheory.OrderThreePrintedMoments
