import MainTheory.Orbit26PrintedProbabilities
import MainTheory.Orbit26AnchorMatrix
import MainTheory.OrderFour26DiagonalRows0
import MainTheory.OrderFour26DiagonalRows1
import MainTheory.OrderFour26DiagonalRows2
import MainTheory.OrderFour26DiagonalRows3
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit26PhysicalMatrices
open scoped BigOperators Matrix
open SixQubit.Orbit26 MainTheory.OrderFour26Support
open MainTheory.Orbit26PrintedProbabilities (bottom_native top_native)
open MainTheory.Orbit26 (cj Jmat)
noncomputable section
def groupIndex (g : Fin 4) (j : Fin 2) : Fin 8 := ⟨2*g.val+j.val,by omega⟩
def C (c : SS.State 6 ℂ) (g : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a j => c (bottomAt (a=1) (groupIndex g j))
def D (d : SS.State 6 ℂ) (g : Fin 4) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a j => d (topAt (a=1) (groupIndex g j))


theorem outer_01 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    cj (C c 0)*Jmat*(D d 1).transpose+
    cj (C c 1)*Jmat*(D d 0).transpose=0 := by
  ext a b
  fin_cases a <;> fin_cases b

  · have hn := SixQubit.Orbit26.outer_g0h2_a0b0 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w6 (by decide +kernel))
    norm_num [C,D,groupIndex,cj,Jmat,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.zero_apply,Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn

  · have hn := SixQubit.Orbit26.outer_g0h2_a0b1 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef12 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef12 w6 (by decide +kernel))
    norm_num [C,D,groupIndex,cj,Jmat,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.zero_apply,Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn

  · have hn := SixQubit.Orbit26.outer_g0h2_a1b0 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef12 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef12 w6 (by decide +kernel))
    norm_num [C,D,groupIndex,cj,Jmat,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.zero_apply,Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn

  · have hn := SixQubit.Orbit26.outer_g0h2_a1b1 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w6 (by decide +kernel))
    norm_num [C,D,groupIndex,cj,Jmat,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.zero_apply,Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn


theorem outer_02 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    cj (C c 0)*Jmat*(D d 2).transpose+
    cj (C c 2)*Jmat*(D d 0).transpose=0 := by
  ext a b
  fin_cases a <;> fin_cases b

  · have hn := SixQubit.Orbit26.outer_g0h1_a0b0 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef7 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef7 w6 (by decide +kernel))
    norm_num [C,D,groupIndex,cj,Jmat,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.zero_apply,Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn

  · have hn := SixQubit.Orbit26.outer_g0h1_a0b1 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef13 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef13 w6 (by decide +kernel))
    norm_num [C,D,groupIndex,cj,Jmat,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.zero_apply,Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn

  · have hn := SixQubit.Orbit26.outer_g0h1_a1b0 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef13 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef13 w6 (by decide +kernel))
    norm_num [C,D,groupIndex,cj,Jmat,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.zero_apply,Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn

  · have hn := SixQubit.Orbit26.outer_g0h1_a1b1 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef7 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef7 w6 (by decide +kernel))
    norm_num [C,D,groupIndex,cj,Jmat,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.zero_apply,Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn


theorem outer_12 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    cj (C c 1)*Jmat*(D d 2).transpose+
    cj (C c 2)*Jmat*(D d 1).transpose=0 := by
  ext a b
  fin_cases a <;> fin_cases b

  · have hn := SixQubit.Orbit26.outer_g1h2_a0b0 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef1 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef1 w6 (by decide +kernel))
    norm_num [C,D,groupIndex,cj,Jmat,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.zero_apply,Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn

  · have hn := SixQubit.Orbit26.outer_g1h2_a0b1 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef11 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef11 w6 (by decide +kernel))
    norm_num [C,D,groupIndex,cj,Jmat,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.zero_apply,Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn

  · have hn := SixQubit.Orbit26.outer_g1h2_a1b0 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef11 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef11 w6 (by decide +kernel))
    norm_num [C,D,groupIndex,cj,Jmat,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.zero_apply,Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn

  · have hn := SixQubit.Orbit26.outer_g1h2_a1b1 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef1 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef1 w6 (by decide +kernel))
    norm_num [C,D,groupIndex,cj,Jmat,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.zero_apply,Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn


theorem bottom_eval : ∀ i : Fin 16,bottom i=(if i.val=0 then MainTheory.OrderEightSupportDisplays.bits 0 else if i.val=1 then MainTheory.OrderEightSupportDisplays.bits 6 else if i.val=2 then MainTheory.OrderEightSupportDisplays.bits 17 else if i.val=3 then MainTheory.OrderEightSupportDisplays.bits 23 else if i.val=4 then MainTheory.OrderEightSupportDisplays.bits 9 else if i.val=5 then MainTheory.OrderEightSupportDisplays.bits 15 else if i.val=6 then MainTheory.OrderEightSupportDisplays.bits 26 else if i.val=7 then MainTheory.OrderEightSupportDisplays.bits 28 else if i.val=8 then MainTheory.OrderEightSupportDisplays.bits 32 else if i.val=9 then MainTheory.OrderEightSupportDisplays.bits 38 else if i.val=10 then MainTheory.OrderEightSupportDisplays.bits 49 else if i.val=11 then MainTheory.OrderEightSupportDisplays.bits 55 else if i.val=12 then MainTheory.OrderEightSupportDisplays.bits 41 else if i.val=13 then MainTheory.OrderEightSupportDisplays.bits 47 else if i.val=14 then MainTheory.OrderEightSupportDisplays.bits 58 else MainTheory.OrderEightSupportDisplays.bits 60) := by decide +kernel
theorem top_eval : ∀ i : Fin 16,top i=(if i.val=0 then MainTheory.OrderEightSupportDisplays.bits 31 else if i.val=1 then MainTheory.OrderEightSupportDisplays.bits 25 else if i.val=2 then MainTheory.OrderEightSupportDisplays.bits 14 else if i.val=3 then MainTheory.OrderEightSupportDisplays.bits 8 else if i.val=4 then MainTheory.OrderEightSupportDisplays.bits 22 else if i.val=5 then MainTheory.OrderEightSupportDisplays.bits 16 else if i.val=6 then MainTheory.OrderEightSupportDisplays.bits 5 else if i.val=7 then MainTheory.OrderEightSupportDisplays.bits 3 else if i.val=8 then MainTheory.OrderEightSupportDisplays.bits 63 else if i.val=9 then MainTheory.OrderEightSupportDisplays.bits 57 else if i.val=10 then MainTheory.OrderEightSupportDisplays.bits 46 else if i.val=11 then MainTheory.OrderEightSupportDisplays.bits 40 else if i.val=12 then MainTheory.OrderEightSupportDisplays.bits 54 else if i.val=13 then MainTheory.OrderEightSupportDisplays.bits 48 else if i.val=14 then MainTheory.OrderEightSupportDisplays.bits 37 else MainTheory.OrderEightSupportDisplays.bits 35) := by decide +kernel

theorem anchor_0 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    (C c 3)ᴴ*D d 0+((C c 0)ᴴ*D d 3).transpose=0 := by
  ext a b
  fin_cases a <;> fin_cases b
  · have hn := SixQubit.Orbit26.anch_i0_j6 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w3 (by decide +kernel))
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.conjTranspose_apply,Matrix.zero_apply,
      Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn
  · have hn := SixQubit.Orbit26.anch_i1_j6 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w2 (by decide +kernel))
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.conjTranspose_apply,Matrix.zero_apply,
      Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn
  · have hn := SixQubit.Orbit26.anch_i0_j7 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w2 (by decide +kernel))
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.conjTranspose_apply,Matrix.zero_apply,
      Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn
  · have hn := SixQubit.Orbit26.anch_i1_j7 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w3 (by decide +kernel))
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.conjTranspose_apply,Matrix.zero_apply,
      Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn

theorem anchor_1 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    (C c 3)ᴴ*D d 1+((C c 1)ᴴ*D d 3).transpose=0 := by
  ext a b
  fin_cases a <;> fin_cases b
  · have hn := SixQubit.Orbit26.anch_i4_j6 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef9 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef9 w3 (by decide +kernel))
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.conjTranspose_apply,Matrix.zero_apply,
      Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn
  · have hn := SixQubit.Orbit26.anch_i5_j6 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef8 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef8 w2 (by decide +kernel))
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.conjTranspose_apply,Matrix.zero_apply,
      Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn
  · have hn := SixQubit.Orbit26.anch_i4_j7 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef8 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef8 w2 (by decide +kernel))
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.conjTranspose_apply,Matrix.zero_apply,
      Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn
  · have hn := SixQubit.Orbit26.anch_i5_j7 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef9 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef9 w3 (by decide +kernel))
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.conjTranspose_apply,Matrix.zero_apply,
      Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn

theorem anchor_2 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    (C c 3)ᴴ*D d 2+((C c 2)ᴴ*D d 3).transpose=0 := by
  ext a b
  fin_cases a <;> fin_cases b
  · have hn := SixQubit.Orbit26.anch_i2_j6 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef6 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef6 w3 (by decide +kernel))
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.conjTranspose_apply,Matrix.zero_apply,
      Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn
  · have hn := SixQubit.Orbit26.anch_i3_j6 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef5 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef5 w2 (by decide +kernel))
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.conjTranspose_apply,Matrix.zero_apply,
      Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn
  · have hn := SixQubit.Orbit26.anch_i2_j7 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef5 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef5 w2 (by decide +kernel))
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.conjTranspose_apply,Matrix.zero_apply,
      Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn
  · have hn := SixQubit.Orbit26.anch_i3_j7 c d
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef6 w0 (by decide +kernel))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef6 w3 (by decide +kernel))
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,
      Matrix.transpose_apply,Matrix.conjTranspose_apply,Matrix.zero_apply,
      Fin.sum_univ_two,bottom_native,top_native]
    simp only [starRingEnd_apply]
    linear_combination hn

theorem moment_0 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    C c 0*(C c 0)ᴴ+D d 0*(D d 0)ᴴ=
      (1/2 : ℂ) • (∑ k : Fin 4,C c k*(C c k)ᴴ) := by
  ext a b
  fin_cases a <;> fin_cases b
  · have hn := MainTheory.OrderFour26DiagonalRows0.Entry00.equation c d hc hd hkl
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,
      Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
      bottomAt,topAt,tailWords]
    norm_num [bottom_eval,top_eval] at hn
    simp only [starRingEnd_apply] at hn ⊢
    linear_combination hn
  · have hn := MainTheory.OrderFour26DiagonalRows0.Entry01.equation c d hc hd hkl
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,
      Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
      bottomAt,topAt,tailWords]
    norm_num [bottom_eval,top_eval] at hn
    simp only [starRingEnd_apply] at hn ⊢
    linear_combination hn
  · have hn := MainTheory.OrderFour26DiagonalRows0.Entry10.equation c d hc hd hkl
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,
      Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
      bottomAt,topAt,tailWords]
    norm_num [bottom_eval,top_eval] at hn
    simp only [starRingEnd_apply] at hn ⊢
    linear_combination hn
  · have hn := MainTheory.OrderFour26DiagonalRows0.Entry11.equation c d hc hd hkl
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,
      Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
      bottomAt,topAt,tailWords]
    norm_num [bottom_eval,top_eval] at hn
    simp only [starRingEnd_apply] at hn ⊢
    linear_combination hn

theorem moment_1 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    C c 1*(C c 1)ᴴ+D d 1*(D d 1)ᴴ=
      (1/2 : ℂ) • (∑ k : Fin 4,C c k*(C c k)ᴴ) := by
  ext a b
  fin_cases a <;> fin_cases b
  · have hn := MainTheory.OrderFour26DiagonalRows1.Entry00.equation c d hc hd hkl
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,
      Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
      bottomAt,topAt,tailWords]
    norm_num [bottom_eval,top_eval] at hn
    simp only [starRingEnd_apply] at hn ⊢
    linear_combination hn
  · have hn := MainTheory.OrderFour26DiagonalRows1.Entry01.equation c d hc hd hkl
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,
      Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
      bottomAt,topAt,tailWords]
    norm_num [bottom_eval,top_eval] at hn
    simp only [starRingEnd_apply] at hn ⊢
    linear_combination hn
  · have hn := MainTheory.OrderFour26DiagonalRows1.Entry10.equation c d hc hd hkl
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,
      Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
      bottomAt,topAt,tailWords]
    norm_num [bottom_eval,top_eval] at hn
    simp only [starRingEnd_apply] at hn ⊢
    linear_combination hn
  · have hn := MainTheory.OrderFour26DiagonalRows1.Entry11.equation c d hc hd hkl
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,
      Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
      bottomAt,topAt,tailWords]
    norm_num [bottom_eval,top_eval] at hn
    simp only [starRingEnd_apply] at hn ⊢
    linear_combination hn

theorem moment_2 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    C c 2*(C c 2)ᴴ+D d 2*(D d 2)ᴴ=
      (1/2 : ℂ) • (∑ k : Fin 4,C c k*(C c k)ᴴ) := by
  ext a b
  fin_cases a <;> fin_cases b
  · have hn := MainTheory.OrderFour26DiagonalRows2.Entry00.equation c d hc hd hkl
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,
      Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
      bottomAt,topAt,tailWords]
    norm_num [bottom_eval,top_eval] at hn
    simp only [starRingEnd_apply] at hn ⊢
    linear_combination hn
  · have hn := MainTheory.OrderFour26DiagonalRows2.Entry01.equation c d hc hd hkl
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,
      Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
      bottomAt,topAt,tailWords]
    norm_num [bottom_eval,top_eval] at hn
    simp only [starRingEnd_apply] at hn ⊢
    linear_combination hn
  · have hn := MainTheory.OrderFour26DiagonalRows2.Entry10.equation c d hc hd hkl
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,
      Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
      bottomAt,topAt,tailWords]
    norm_num [bottom_eval,top_eval] at hn
    simp only [starRingEnd_apply] at hn ⊢
    linear_combination hn
  · have hn := MainTheory.OrderFour26DiagonalRows2.Entry11.equation c d hc hd hkl
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,
      Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
      bottomAt,topAt,tailWords]
    norm_num [bottom_eval,top_eval] at hn
    simp only [starRingEnd_apply] at hn ⊢
    linear_combination hn

theorem moment_3 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    C c 3*(C c 3)ᴴ+D d 3*(D d 3)ᴴ=
      (1/2 : ℂ) • (∑ k : Fin 4,C c k*(C c k)ᴴ) := by
  ext a b
  fin_cases a <;> fin_cases b
  · have hn := MainTheory.OrderFour26DiagonalRows3.Entry00.equation c d hc hd hkl
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,
      Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
      bottomAt,topAt,tailWords]
    norm_num [bottom_eval,top_eval] at hn
    simp only [starRingEnd_apply] at hn ⊢
    linear_combination hn
  · have hn := MainTheory.OrderFour26DiagonalRows3.Entry01.equation c d hc hd hkl
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,
      Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
      bottomAt,topAt,tailWords]
    norm_num [bottom_eval,top_eval] at hn
    simp only [starRingEnd_apply] at hn ⊢
    linear_combination hn
  · have hn := MainTheory.OrderFour26DiagonalRows3.Entry10.equation c d hc hd hkl
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,
      Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
      bottomAt,topAt,tailWords]
    norm_num [bottom_eval,top_eval] at hn
    simp only [starRingEnd_apply] at hn ⊢
    linear_combination hn
  · have hn := MainTheory.OrderFour26DiagonalRows3.Entry11.equation c d hc hd hkl
    norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.add_apply,Matrix.conjTranspose_apply,
      Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
      bottomAt,topAt,tailWords]
    norm_num [bottom_eval,top_eval] at hn
    simp only [starRingEnd_apply] at hn ⊢
    linear_combination hn

theorem physical_anchor (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (g : Fin 3) :
    (C c 3)ᴴ*D d g.castSucc+((C c g.castSucc)ᴴ*D d 3).transpose=0 := by
  fin_cases g
  · exact anchor_0 c d hc hd hkl
  · exact anchor_1 c d hc hd hkl
  · exact anchor_2 c d hc hd hkl

theorem physical_moment (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (g : Fin 4) :
    C c g*(C c g)ᴴ+D d g*(D d g)ᴴ=
      (1/2 : ℂ) • (∑ k : Fin 4,C c k*(C c k)ᴴ) := by
  fin_cases g
  · exact moment_0 c d hc hd hkl
  · exact moment_1 c d hc hd hkl
  · exact moment_2 c d hc hd hkl
  · exact moment_3 c d hc hd hkl

theorem physical_rho (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∑ k : Fin 4,C c k*(C c k)ᴴ)=(∑ k : Fin 4,D d k*(D d k)ᴴ) := by
  ext a b
  have h0 := congrArg (fun X => X a b) (moment_0 c d hc hd hkl)
  have h1 := congrArg (fun X => X a b) (moment_1 c d hc hd hkl)
  have h2 := congrArg (fun X => X a b) (moment_2 c d hc hd hkl)
  have h3 := congrArg (fun X => X a b) (moment_3 c d hc hd hkl)
  norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.add_apply,Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
    bottomAt,topAt,tailWords] at h0 h1 h2 h3 ⊢
  linear_combination -h0-h1-h2-h3

theorem physical_outer (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (g h : Fin 3) (hgh : g<h) :
    cj (C c g.castSucc)*Jmat*(D d h.castSucc).transpose+
    cj (C c h.castSucc)*Jmat*(D d g.castSucc).transpose=0 := by
  fin_cases g <;> fin_cases h
  all_goals simp only [Fin.lt_def] at hgh
  all_goals norm_num at hgh
  all_goals first | exact outer_01 c d hc hd hkl | exact outer_02 c d hc hd hkl | exact outer_12 c d hc hd hkl
end
end MainTheory.Orbit26PhysicalMatrices
