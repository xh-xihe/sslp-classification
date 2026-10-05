import SixQubit.CodeOrbit27
import SixQubit.CodeOrbit62
import MainTheory.FlipCharacterObstruction

/-! The literal six-edge matrix and the particular odd triangle printed
in the current SI. Intermediate statements use diagonal moments and actual
physical cross rows, independently of the pre-existing no-code theorems.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.OrderFourWalshRemainingDisplays
open scoped BigOperators Matrix
noncomputable section

namespace Orbit27
open SixQubit.Orbit27

theorem consequence0 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) : q0=(3/8) := by
  linear_combination 1 * hm.n0 + (-5/8) * hm.n1 + (-5/8) * hm.m1 + (-5/8) * hm.m2 + (-5/8) * hm.m3 + (-5/8) * hm.m4 + (-5/8) * hm.m5 + (-5/8) * hm.m6 + (1/4) * hm.c12 + (1/4) * hm.c13 + (1/4) * hm.c14 + (1/4) * hm.c15 + (1/4) * hm.c16 + (1/4) * hm.c23 + (1/4) * hm.c24 + (1/4) * hm.c25 + (1/4) * hm.c26 + (1/4) * hm.c34 + (1/4) * hm.c35 + (1/4) * hm.c36 + (1/4) * hm.c45 + (1/4) * hm.c46 + (1/4) * hm.c56

theorem consequence1 {q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 q15 r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11) : r0 + r1 + r2 + r3 + r4 + r6=(5/8) := by
  linear_combination (5/8) * hm.n1 + (-3/8) * hm.m1 + (-3/8) * hm.m2 + (-3/8) * hm.m3 + (-3/8) * hm.m4 + (-3/8) * hm.m5 + (-3/8) * hm.m6 + (1/4) * hm.c12 + (1/4) * hm.c13 + (1/4) * hm.c14 + (1/4) * hm.c15 + (1/4) * hm.c16 + (1/4) * hm.c23 + (1/4) * hm.c24 + (1/4) * hm.c25 + (1/4) * hm.c26 + (1/4) * hm.c34 + (1/4) * hm.c35 + (1/4) * hm.c36 + (1/4) * hm.c45 + (1/4) * hm.c46 + (1/4) * hm.c56

theorem physical_probabilities (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (Complex.normSq (c y0))=(3/8) ∧
    (Complex.normSq (d z0)) + (Complex.normSq (d z1)) + (Complex.normSq (d z2)) + (Complex.normSq (d z3)) + (Complex.normSq (d z4)) + (Complex.normSq (d z6))=(5/8) := by
  have hm := moments c d hc hd hnc hnd hkl
  exact ⟨consequence0 hm,consequence1 hm⟩

def sources : Fin 6 → SS.BitString 6 := ![z6,z7,z8,z9,z10,z11]
def destinations : Fin 6 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5]
def characters : Fin 6 → SS.BitString 6 := ![w0_0,w0_1,w0_2,w0_3,w0_4,w0_5]
def W : Matrix (Fin 6) (Fin 6) ℚ :=
  !![1,1,1,1,1,1;1,1,-1,-1,-1,-1;1,-1,1,-1,-1,-1;
    1,-1,-1,1,-1,-1;1,-1,-1,-1,1,-1;1,-1,-1,-1,-1,1]
def WC : Matrix (Fin 6) (Fin 6) ℂ := fun i j => W i j
def products (c d : SS.State 6 ℂ) : Fin 6 → ℂ :=
  fun j => star (c (destinations j))*d (sources j)
theorem actual_characters : ∀ i j,
    W i j=if SS.bdot (characters i) (sources j) then -1 else 1 := by decide +kernel
theorem actual_incidence : S1.filter (fun y => SS.bxor y ef0 ∈ S0)=
    Finset.univ.image sources := by decide +kernel
theorem actual_images : ∀ j, SS.bxor (sources j) ef0=destinations j := by decide +kernel
theorem weights : ∀ i, (⟨ef0,characters i⟩ : SS.PauliString 6).wt≤2 := by decide +kernel
theorem determinant : W.det= -128 := by decide +kernel
theorem determinant_complex : WC.det= -128 := by
  have he : WC.det=(W.det : ℂ) := ((algebraMap ℚ ℂ).map_det W).symm
  rw [he,determinant]
  norm_num
theorem expansion (c d : SS.State 6 ℂ) : ∀ i,
    offSum c d ef0 (characters i)=(WC.mulVec (products c d)) i := by
  intro i
  fin_cases i
  · rw [show characters ⟨0,by decide⟩=w0_0 from rfl,ex0_0]
    norm_num [WC,W,products,sources,destinations,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    ring
  · rw [show characters ⟨1,by decide⟩=w0_1 from rfl,ex0_1]
    norm_num [WC,W,products,sources,destinations,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    ring
  · rw [show characters ⟨2,by decide⟩=w0_2 from rfl,ex0_2]
    norm_num [WC,W,products,sources,destinations,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    ring
  · rw [show characters ⟨3,by decide⟩=w0_3 from rfl,ex0_3]
    norm_num [WC,W,products,sources,destinations,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    ring
  · rw [show characters ⟨4,by decide⟩=w0_4 from rfl,ex0_4]
    norm_num [WC,W,products,sources,destinations,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    ring
  · rw [show characters ⟨5,by decide⟩=w0_5 from rfl,ex0_5]
    norm_num [WC,W,products,sources,destinations,Matrix.mulVec,dotProduct,Fin.sum_univ_succ]
    ring
theorem physical_matrix_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : WC.mulVec (products c d)=0 := by
  ext i
  rw [← expansion]
  exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl _ _ (weights i)
theorem physical_all_edges_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : products c d=0 := by
  have hdW : IsUnit WC.det := by rw [determinant_complex]; norm_num
  calc products c d=(WC⁻¹*WC).mulVec (products c d) := by rw [Matrix.nonsing_inv_mul _ hdW,Matrix.one_mulVec]
    _=WC⁻¹ *ᵥ (WC *ᵥ products c d) := by rw [Matrix.mulVec_mulVec]
    _=0 := by rw [physical_matrix_rows c d hc hd hkl,Matrix.mulVec_zero]

namespace AllCoordinates
def sources (i : Fin 6) : Fin 6 → SS.BitString 6 :=
  Fin.cases (SS.stdBasis i) (fun j : Fin 5 => SS.complement (SS.stdBasis (i.succAbove j)))
def characters (i : Fin 6) : Fin 6 → SS.BitString 6 :=
  Fin.cases (fun _ => false) (fun j : Fin 5 => SS.stdBasis (i.succAbove j))
theorem injective : ∀ i, Function.Injective (sources i) := by decide +kernel
theorem incidence : ∀ i, Finset.univ.image (sources i)=
    S1.filter (fun y => SS.bxor y (SS.stdBasis i) ∈ S0) := by decide +kernel
theorem characters_checked : ∀ i j k,
    W j k=if SS.bdot (characters i j) (sources i k) then -1 else 1 := by decide +kernel
theorem weight_checked : ∀ i j, (⟨SS.stdBasis i,characters i j⟩ : SS.PauliString 6).wt≤2 := by decide +kernel
theorem matrix_checked (i : Fin 6) :
    MainTheory.FlipCharacter.restrictedCharacterMatrix (characters i) (sources i)=WC := by
  ext j k
  change (if SS.bdot (characters i j) (sources i k) then (-1 : ℂ) else 1)=(W j k : ℂ)
  rw [characters_checked i j k]
  split <;> norm_num
theorem first_source : ∀ i, sources i 0=SS.stdBasis i ∧
    SS.bxor (sources i 0) (SS.stdBasis i)=y0 := by decide +kernel
theorem physical_products_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (i : Fin 6) : ∀ j,
    star (c (SS.bxor (sources i j) (SS.stdBasis i)))*d (sources i j)=0 := by
  apply MainTheory.FlipCharacter.monomials_zero_of_det_ne_zero S0 S1 c d hc hd hkl
    (SS.stdBasis i) (characters i) (sources i) (injective i) (incidence i) (weight_checked i)
  rw [matrix_checked,determinant_complex]
  norm_num
theorem physical_weight_one_zero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ i, d (SS.stdBasis i)=0 := by
  have hp := (physical_probabilities c d hc hd hnc hnd hkl).1
  have hn : c y0≠0 := by intro he; rw [he,Complex.normSq_zero] at hp; norm_num at hp
  intro i
  have he := physical_products_zero c d hc hd hkl i 0
  rw [(first_source i).2,(first_source i).1] at he
  exact (mul_eq_zero.1 he).resolve_left (star_ne_zero.2 hn)
end AllCoordinates

end Orbit27

namespace Orbit62
open SixQubit.Orbit62

theorem consequence0 {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) : q0=(1/4) := by
  linear_combination 1 * hm.n0 + (-3/4) * hm.n1 + (-11/8) * hm.m1 + (1/8) * hm.m2 + (1/8) * hm.m3 + (-3/8) * hm.m4 + (-3/8) * hm.m5 + (-3/8) * hm.m6 + (1/2) * hm.c12 + (1/2) * hm.c13 + (1/2) * hm.c14 + (1/2) * hm.c15 + (1/2) * hm.c16 + -1 * hm.c23

theorem consequence1 {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) : q1=(1/8) := by
  linear_combination (1/8) * hm.n1 + (-3/16) * hm.m1 + (-3/16) * hm.m2 + (13/16) * hm.m3 + (1/16) * hm.m4 + (1/16) * hm.m5 + (1/16) * hm.m6 + (1/2) * hm.c12 + (-1/2) * hm.c13 + (-1/2) * hm.c23

theorem consequence2 {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) : q2=(1/8) := by
  linear_combination (1/8) * hm.n1 + (-3/16) * hm.m1 + (13/16) * hm.m2 + (-3/16) * hm.m3 + (1/16) * hm.m4 + (1/16) * hm.m5 + (1/16) * hm.m6 + (-1/2) * hm.c12 + (1/2) * hm.c13 + (-1/2) * hm.c23

theorem consequence3 {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) : q3=(1/8) := by
  linear_combination (1/8) * hm.n1 + (13/16) * hm.m1 + (-3/16) * hm.m2 + (-3/16) * hm.m3 + (1/16) * hm.m4 + (1/16) * hm.m5 + (1/16) * hm.m6 + (-1/2) * hm.c12 + (-1/2) * hm.c13 + (1/2) * hm.c23

theorem consequence4 {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) : q4=(1/8) := by
  linear_combination (1/8) * hm.n1 + (5/16) * hm.m1 + (-3/16) * hm.m2 + (-3/16) * hm.m3 + (1/16) * hm.m4 + (1/16) * hm.m5 + (1/16) * hm.m6 + (-1/2) * hm.c14 + (-1/2) * hm.c15 + (1/2) * hm.c16 + (1/2) * hm.c23

theorem consequence5 {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) : q5=(1/8) := by
  linear_combination (1/8) * hm.n1 + (5/16) * hm.m1 + (-3/16) * hm.m2 + (-3/16) * hm.m3 + (1/16) * hm.m4 + (1/16) * hm.m5 + (1/16) * hm.m6 + (-1/2) * hm.c14 + (1/2) * hm.c15 + (-1/2) * hm.c16 + (1/2) * hm.c23

theorem consequence6 {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) : q6=(1/8) := by
  linear_combination (1/8) * hm.n1 + (5/16) * hm.m1 + (-3/16) * hm.m2 + (-3/16) * hm.m3 + (1/16) * hm.m4 + (1/16) * hm.m5 + (1/16) * hm.m6 + (1/2) * hm.c14 + (-1/2) * hm.c15 + (-1/2) * hm.c16 + (1/2) * hm.c23

theorem consequence7 {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) : r0=(1/8) := by
  linear_combination (1/8) * hm.n1 + (-3/16) * hm.m1 + (5/16) * hm.m2 + (5/16) * hm.m3 + (9/16) * hm.m4 + (-7/16) * hm.m5 + (-7/16) * hm.m6 + (-1/2) * hm.c14 + (1/2) * hm.c15 + (1/2) * hm.c16 + (-1/2) * hm.c23

theorem consequence8 {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) : r1=(1/8) := by
  linear_combination (1/8) * hm.n1 + (-3/16) * hm.m1 + (5/16) * hm.m2 + (5/16) * hm.m3 + (-7/16) * hm.m4 + (9/16) * hm.m5 + (-7/16) * hm.m6 + (1/2) * hm.c14 + (-1/2) * hm.c15 + (1/2) * hm.c16 + (-1/2) * hm.c23

theorem consequence9 {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) : r2=(1/8) := by
  linear_combination (1/8) * hm.n1 + (-3/16) * hm.m1 + (5/16) * hm.m2 + (5/16) * hm.m3 + (-7/16) * hm.m4 + (-7/16) * hm.m5 + (9/16) * hm.m6 + (1/2) * hm.c14 + (1/2) * hm.c15 + (-1/2) * hm.c16 + (-1/2) * hm.c23

theorem consequence10 {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) : r3=(1/8) := by
  linear_combination (1/8) * hm.n1 + (-3/16) * hm.m1 + (-3/16) * hm.m2 + (-3/16) * hm.m3 + (1/16) * hm.m4 + (1/16) * hm.m5 + (1/16) * hm.m6 + (1/2) * hm.c12 + (1/2) * hm.c13 + (-1/2) * hm.c23

theorem consequence11 {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) : r4=(1/8) := by
  linear_combination (1/8) * hm.n1 + (-3/16) * hm.m1 + (-3/16) * hm.m2 + (-3/16) * hm.m3 + (1/16) * hm.m4 + (1/16) * hm.m5 + (1/16) * hm.m6 + (1/2) * hm.c12 + (-1/2) * hm.c13 + (1/2) * hm.c23

theorem consequence12 {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) : r5=(1/8) := by
  linear_combination (1/8) * hm.n1 + (-3/16) * hm.m1 + (-3/16) * hm.m2 + (-3/16) * hm.m3 + (1/16) * hm.m4 + (1/16) * hm.m5 + (1/16) * hm.m6 + (-1/2) * hm.c12 + (1/2) * hm.c13 + (1/2) * hm.c23

theorem consequence13 {q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6 : ℝ}
    (hm : MomentSystem q0 q1 q2 q3 q4 q5 q6 r0 r1 r2 r3 r4 r5 r6) : r6=(1/4) := by
  linear_combination (1/4) * hm.n1 + (9/8) * hm.m1 + (-3/8) * hm.m2 + (-3/8) * hm.m3 + (1/8) * hm.m4 + (1/8) * hm.m5 + (1/8) * hm.m6 + (-1/2) * hm.c12 + (-1/2) * hm.c13 + (-1/2) * hm.c14 + (-1/2) * hm.c15 + (-1/2) * hm.c16 + 1 * hm.c23

theorem physical_probabilities (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (Complex.normSq (c y0))=(1/4) ∧
    (Complex.normSq (c y1))=(1/8) ∧
    (Complex.normSq (c y2))=(1/8) ∧
    (Complex.normSq (c y3))=(1/8) ∧
    (Complex.normSq (c y4))=(1/8) ∧
    (Complex.normSq (c y5))=(1/8) ∧
    (Complex.normSq (c y6))=(1/8) ∧
    (Complex.normSq (d z0))=(1/8) ∧
    (Complex.normSq (d z1))=(1/8) ∧
    (Complex.normSq (d z2))=(1/8) ∧
    (Complex.normSq (d z3))=(1/8) ∧
    (Complex.normSq (d z4))=(1/8) ∧
    (Complex.normSq (d z5))=(1/8) ∧
    (Complex.normSq (d z6))=(1/4) := by
  have hm := moments c d hc hd hnc hnd hkl
  exact ⟨consequence0 hm,consequence1 hm,consequence2 hm,consequence3 hm,consequence4 hm,consequence5 hm,consequence6 hm,consequence7 hm,consequence8 hm,consequence9 hm,consequence10 hm,consequence11 hm,consequence12 hm,consequence13 hm⟩

def bottom : Fin 7 → SS.BitString 6 := ![y0,y1,y2,y3,y4,y5,y6]
def top : Fin 7 → SS.BitString 6 := ![z6,z5,z4,z3,z2,z1,z0]
def triangle : Fin 3 → SS.BitString 6 := ![y0,y6,y2]
def next : Fin 3 → Fin 3 := ![1,2,0]
def flips : Fin 3 → SS.BitString 6 :=
  ![bs false false false false true true,bs false true false true false false,bs true false true false false false]
def zero : SS.BitString 6 := fun _ => false
def rho (c d : SS.State 6 ℂ) (x : SS.BitString 6) : ℂ := d (SS.complement x)/star (c x)
theorem actual_complements : ∀ i, top i=SS.complement (bottom i) := by decide +kernel
theorem actual_incidence : ∀ k,
    S1.filter (fun y => SS.bxor y (flips k) ∈ S0)=
    {SS.complement (triangle k),SS.complement (triangle (next k))} := by decide +kernel
theorem pairs_ne : ∀ k, SS.complement (triangle k)≠SS.complement (triangle (next k)) := by decide +kernel
theorem actual_images : ∀ k,
    SS.bxor (SS.complement (triangle k)) (flips k)=triangle (next k) ∧
    SS.bxor (SS.complement (triangle (next k))) (flips k)=triangle k := by decide +kernel
theorem zero_signs : ∀ k, SS.bdot zero (SS.complement (triangle k))=false ∧
    SS.bdot zero (SS.complement (triangle (next k)))=false := by decide +kernel
theorem weights : ∀ k, (⟨flips k,zero⟩ : SS.PauliString 6).wt≤2 := by decide +kernel
theorem expansion (c d : SS.State 6 ℂ) (k : Fin 3) :
    offSum c d (flips k) zero=
    star (c (triangle k))*d (SS.complement (triangle (next k)))+
    star (c (triangle (next k)))*d (SS.complement (triangle k)) := by
  unfold offSum
  rw [actual_incidence,Finset.sum_pair (pairs_ne k),(actual_images k).1,(actual_images k).2]
  simp only [(zero_signs k).1,(zero_signs k).2,SixQubit.signMul_false]
  ring
theorem reciprocal_opposition (a b da db : ℂ) (ha : a≠0) (hb : b≠0)
    (he : star a*db+star b*da=0) : db/star b= -(da/star a) := by
  apply (div_eq_iff (star_ne_zero.2 hb)).2
  field_simp [ha] at he ⊢
  linear_combination he
theorem physical_triangle_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ k,
    star (c (triangle k))*d (SS.complement (triangle (next k)))+
    star (c (triangle (next k)))*d (SS.complement (triangle k))=0 := by
  intro k
  rw [← expansion]
  exact SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl _ _ (weights k)
theorem physical_all_nonzero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ i, c (bottom i)≠0 ∧ d (top i)≠0 := by
  have hm := moments c d hc hd hnc hnd hkl
  intro i
  fin_cases i
  · constructor
    · intro he
      have hp := consequence0 hm
      norm_num [bottom] at he
      rw [he,Complex.normSq_zero] at hp
      norm_num at hp
    · intro he
      have hp := consequence13 hm
      norm_num [top] at he
      rw [he,Complex.normSq_zero] at hp
      norm_num at hp
  · constructor
    · intro he
      have hp := consequence1 hm
      norm_num [bottom] at he
      rw [he,Complex.normSq_zero] at hp
      norm_num at hp
    · intro he
      have hp := consequence12 hm
      norm_num [top] at he
      rw [he,Complex.normSq_zero] at hp
      norm_num at hp
  · constructor
    · intro he
      have hp := consequence2 hm
      norm_num [bottom] at he
      rw [he,Complex.normSq_zero] at hp
      norm_num at hp
    · intro he
      have hp := consequence11 hm
      norm_num [top] at he
      rw [he,Complex.normSq_zero] at hp
      norm_num at hp
  · constructor
    · intro he
      have hp := consequence3 hm
      norm_num [bottom] at he
      rw [he,Complex.normSq_zero] at hp
      norm_num at hp
    · intro he
      have hp := consequence10 hm
      norm_num [top] at he
      rw [he,Complex.normSq_zero] at hp
      norm_num at hp
  · constructor
    · intro he
      have hp := consequence4 hm
      norm_num [bottom] at he
      rw [he,Complex.normSq_zero] at hp
      norm_num at hp
    · intro he
      have hp := consequence9 hm
      norm_num [top] at he
      rw [he,Complex.normSq_zero] at hp
      norm_num at hp
  · constructor
    · intro he
      have hp := consequence5 hm
      norm_num [bottom] at he
      rw [he,Complex.normSq_zero] at hp
      norm_num at hp
    · intro he
      have hp := consequence8 hm
      norm_num [top] at he
      rw [he,Complex.normSq_zero] at hp
      norm_num at hp
  · constructor
    · intro he
      have hp := consequence6 hm
      norm_num [bottom] at he
      rw [he,Complex.normSq_zero] at hp
      norm_num at hp
    · intro he
      have hp := consequence7 hm
      norm_num [top] at he
      rw [he,Complex.normSq_zero] at hp
      norm_num at hp
theorem triangle_mem : ∀ k, ∃ i, triangle k=bottom i := by decide +kernel
theorem physical_phase_triangle (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ k,
    rho c d (triangle (next k))= -rho c d (triangle k) := by
  have hn := physical_all_nonzero c d hc hd hnc hnd hkl
  have ht : ∀ k, c (triangle k)≠0 := by
    intro k
    obtain ⟨i,hi⟩ := triangle_mem k
    rw [hi]
    exact (hn i).1
  intro k
  exact reciprocal_opposition _ _ _ _ (ht k) (ht (next k))
    (physical_triangle_rows c d hc hd hkl k)

end Orbit62

end
end MainTheory.OrderFourWalshRemainingDisplays
