import MainTheory.ComplementaryPhasePair
import MainTheory.GridSupportAlgebra
import MainTheory.OrderFivePrintedMoments

/-! Actual physical grid labels, hub phases and full support in the printed SI.
Every intermediate step retains zero amplitudes until positivity is proved.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace MainTheory.OrderFiveGridRemainingDisplays
open scoped BigOperators
noncomputable section
open MainTheory.ComplementaryPhasePair

namespace Orbit38
open SixQubit.Orbit38
def A := MainTheory.OrderFivePrintedMoments.Orbit38.A
def B := MainTheory.OrderFivePrintedMoments.Orbit38.B
def topGrid : Fin 2 → Fin 4 → SS.BitString 6 := ![![z8,z7,z6,z5],![z4,z3,z2,z1]]
def b (c : SS.State 6 ℂ) : Fin 2 → Fin 4 → ℂ := fun i j => c (B i j)
def db (d : SS.State 6 ℂ) : Fin 2 → Fin 4 → ℂ := fun i j => d (topGrid i j)
def phaseS (c d : SS.State 6 ℂ) : ℂ := sigma (c y12) (d z0)
def rowSupport (c : SS.State 6 ℂ) := MainTheory.GridSupportAlgebra.rowSupport (b c)

theorem literal_labels :
    S0=(Finset.univ.image A ∪ Finset.univ.image (fun p : Fin 2 × Fin 4 => B p.1 p.2)) ∪ {y12} ∧
    (∀ i j, SS.complement (B i j)=topGrid i j) ∧ SS.complement y12=z0 := by decide +kernel

theorem physical_hub (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ i j,
    star (b c i j)*d z0+star (c y12)*db d i j=0 := by
  intro i j
  fin_cases i <;> fin_cases j
  · have he := rec11 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef9 w0 (by decide))
    simpa [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] using he
  · have he := rec12 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef8 w0 (by decide))
    simpa [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] using he
  · have he := rec13 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef7 w0 (by decide))
    simpa [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] using he
  · have he := rec14 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef6 w0 (by decide))
    simpa [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] using he
  · have he := rec21 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef13 w0 (by decide))
    simpa [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] using he
  · have he := rec22 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef12 w0 (by decide))
    simpa [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] using he
  · have he := rec23 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef11 w0 (by decide))
    simpa [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] using he
  · have he := rec24 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef10 w0 (by decide))
    simpa [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] using he

theorem physical_star_nonzero (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : c y12≠0 ∧ d z0≠0 := by
  have hn := (moments c d hc hd hnc hnd hkl).facts
  constructor
  · intro he
    have hs := hn.1
    rw [he,Complex.normSq_zero] at hs
    norm_num at hs
  · intro he
    have hs := hn.2.1
    rw [he,Complex.normSq_zero] at hs
    norm_num at hs

theorem physical_weighted_phases (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ i j,
    star (db d i j)= -phaseS c d*b c i j := by
  intro i j
  exact weighted_opposition _ _ _ _ (physical_star_nonzero c d hc hd hnc hnd hkl).1
    (physical_hub c d hc hd hkl i j)

theorem physical_common_phase (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (i : Fin 2) (j : Fin 4) (hj : b c i j≠0) :
    sigma (b c i j) (db d i j)= -phaseS c d :=
  active_opposition _ _ _ _ hj (physical_star_nonzero c d hc hd hnc hnd hkl).1
    (physical_hub c d hc hd hkl i j)

theorem physical_rectangle (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (j k : Fin 4) (hne : j≠k) :
    star (b c 0 j)*db d 1 k+star (b c 0 k)*db d 1 j+
      star (b c 1 j)*db d 0 k+star (b c 1 k)*db d 0 j=0 := by
  fin_cases j <;> fin_cases k
  · exact False.elim (hne rfl)
  · have he : offSum c d ef0 w0=0 := (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef0 w0 (by decide))
    rw [ex0] at he
    norm_num [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] at he ⊢
    linear_combination he
  · have he : offSum c d ef1 w0=0 := (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef1 w0 (by decide))
    rw [ex1] at he
    norm_num [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] at he ⊢
    linear_combination he
  · have he : offSum c d ef2 w0=0 := (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w0 (by decide))
    rw [ex2] at he
    norm_num [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] at he ⊢
    linear_combination he
  · have he : offSum c d ef0 w0=0 := (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef0 w0 (by decide))
    rw [ex0] at he
    norm_num [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] at he ⊢
    linear_combination he
  · exact False.elim (hne rfl)
  · have he : offSum c d ef3 w0=0 := (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w0 (by decide))
    rw [ex3] at he
    norm_num [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] at he ⊢
    linear_combination he
  · have he : offSum c d ef4 w0=0 := (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w0 (by decide))
    rw [ex4] at he
    norm_num [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] at he ⊢
    linear_combination he
  · have he : offSum c d ef1 w0=0 := (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef1 w0 (by decide))
    rw [ex1] at he
    norm_num [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] at he ⊢
    linear_combination he
  · have he : offSum c d ef3 w0=0 := (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w0 (by decide))
    rw [ex3] at he
    norm_num [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] at he ⊢
    linear_combination he
  · exact False.elim (hne rfl)
  · have he : offSum c d ef5 w0=0 := (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef5 w0 (by decide))
    rw [ex5] at he
    norm_num [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] at he ⊢
    linear_combination he
  · have he : offSum c d ef2 w0=0 := (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w0 (by decide))
    rw [ex2] at he
    norm_num [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] at he ⊢
    linear_combination he
  · have he : offSum c d ef4 w0=0 := (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w0 (by decide))
    rw [ex4] at he
    norm_num [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] at he ⊢
    linear_combination he
  · have he : offSum c d ef5 w0=0 := (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef5 w0 (by decide))
    rw [ex5] at he
    norm_num [b,db,B,topGrid,MainTheory.OrderFivePrintedMoments.Orbit38.B] at he ⊢
    linear_combination he
  · exact False.elim (hne rfl)

theorem physical_permanents (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : ∀ j k, j≠k →
    b c 0 j*b c 1 k+b c 0 k*b c 1 j=0 := by
  intro j k hne
  have hn := physical_star_nonzero c d hc hd hnc hnd hkl
  have hk : -phaseS c d≠0 := neg_ne_zero.2 (div_ne_zero (star_ne_zero.2 hn.2) hn.1)
  have hw := physical_weighted_phases c d hc hd hnc hnd hkl
  exact MainTheory.GridSupportAlgebra.permanent_from_weighted_phase _ _ _ _ _ _ _ _ _ hk
    (hw 0 j) (hw 0 k) (hw 1 j) (hw 1 k) (physical_rectangle c d hc hd hkl j k hne)

theorem physical_supports_full (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : rowSupport c 0=Finset.univ ∧ rowSupport c 1=Finset.univ := by
  apply MainTheory.GridSupportAlgebra.supports_univ
  · intro i
    apply MainTheory.GridSupportAlgebra.nonempty_of_mass
    have he := (MainTheory.OrderFivePrintedMoments.Orbit38.physical_display c d hc hd hnc hnd hkl).2.1 i
    change (∑ j, Complex.normSq (c (MainTheory.OrderFivePrintedMoments.Orbit38.B i j)))>0
    rw [he]
    norm_num
  · intro j
    by_contra hh
    push_neg at hh
    have hp := (MainTheory.OrderFivePrintedMoments.Orbit38.physical_column_positive c d hc hd hnc hnd hkl j).2
    change 0<Complex.normSq (b c 0 j)+Complex.normSq (b c 1 j) at hp
    rw [hh.1,hh.2] at hp
    norm_num at hp
  · exact physical_permanents c d hc hd hnc hnd hkl
end Orbit38

namespace Orbit37
open SixQubit.Orbit37
def A := MainTheory.OrderFivePrintedMoments.Orbit37.A
def B := MainTheory.OrderFivePrintedMoments.Orbit37.B
def topA : Fin 3 → SS.BitString 6 := ![z10,z11,z12]
def topB : Fin 3 → Fin 3 → SS.BitString 6 := ![![z9,z8,z7],![z6,z5,z4],![z3,z2,z1]]
def activeColumns (c : SS.State 6 ℂ) : Finset (Fin 3) := Finset.univ.filter (fun j => c (A j)≠0)
def rowSupport (c : SS.State 6 ℂ) (i : Fin 3) := (activeColumns c).filter (fun j => c (B i j)≠0)
theorem actual_complements : (∀ j, SS.complement (A j)=topA j) ∧
    (∀ i j, SS.complement (B i j)=topB i j) ∧ SS.complement y12=z0 := by decide +kernel

theorem physical_reciprocal (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (j : Fin 3) :
    star (c (A j))*d z0+star (c y12)*d (topA j)=0 := by
  fin_cases j
  · have he := rec3 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef1 w0 (by decide))
    simpa [A,topA,MainTheory.OrderFivePrintedMoments.Orbit37.A] using he
  · have he := rec2 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w0 (by decide))
    simpa [A,topA,MainTheory.OrderFivePrintedMoments.Orbit37.A] using he
  · have he := rec1 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef0 w0 (by decide))
    simpa [A,topA,MainTheory.OrderFivePrintedMoments.Orbit37.A] using he

theorem physical_sync (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (i j : Fin 3) :
    star (c (A j))*d (topB i j)=star (c (B i j))*d (topA j) := by
  fin_cases i <;> fin_cases j
  · have he := sync1_3 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef11 w11 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef11 w2 (by decide))
    simpa [A,B,topA,topB,MainTheory.OrderFivePrintedMoments.Orbit37.A,MainTheory.OrderFivePrintedMoments.Orbit37.B] using he
  · have he := sync1_2 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef11 w4 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef11 w2 (by decide))
    simpa [A,B,topA,topB,MainTheory.OrderFivePrintedMoments.Orbit37.A,MainTheory.OrderFivePrintedMoments.Orbit37.B] using he
  · have he := sync1_1 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef11 w11 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef11 w4 (by decide))
    simpa [A,B,topA,topB,MainTheory.OrderFivePrintedMoments.Orbit37.A,MainTheory.OrderFivePrintedMoments.Orbit37.B] using he
  · have he := sync2_3 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef7 w15 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef7 w2 (by decide))
    simpa [A,B,topA,topB,MainTheory.OrderFivePrintedMoments.Orbit37.A,MainTheory.OrderFivePrintedMoments.Orbit37.B] using he
  · have he := sync2_2 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef7 w4 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef7 w2 (by decide))
    simpa [A,B,topA,topB,MainTheory.OrderFivePrintedMoments.Orbit37.A,MainTheory.OrderFivePrintedMoments.Orbit37.B] using he
  · have he := sync2_1 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef7 w15 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef7 w4 (by decide))
    simpa [A,B,topA,topB,MainTheory.OrderFivePrintedMoments.Orbit37.A,MainTheory.OrderFivePrintedMoments.Orbit37.B] using he
  · have he := sync3_3 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w15 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w2 (by decide))
    simpa [A,B,topA,topB,MainTheory.OrderFivePrintedMoments.Orbit37.A,MainTheory.OrderFivePrintedMoments.Orbit37.B] using he
  · have he := sync3_2 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w4 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w2 (by decide))
    simpa [A,B,topA,topB,MainTheory.OrderFivePrintedMoments.Orbit37.A,MainTheory.OrderFivePrintedMoments.Orbit37.B] using he
  · have he := sync3_1 c d (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w15 (by decide))
      (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w4 (by decide))
    simpa [A,B,topA,topB,MainTheory.OrderFivePrintedMoments.Orbit37.A,MainTheory.OrderFivePrintedMoments.Orbit37.B] using he

theorem physical_active_column_phase (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (i j : Fin 3)
    (ha : c (A j)≠0) (hb : c (B i j)≠0) :
    sigma (c (B i j)) (d (topB i j))=sigma (c (A j)) (d (topA j)) ∧
      sigma (c (A j)) (d (topA j))= -sigma (c y12) (d z0) := by
  have hm := moments c d hc hd hnc hnd hkl
  have hs : c y12≠0 := by
    intro he
    have hx := MainTheory.OrderFivePrintedMoments.Orbit37.consequence0 hm
    rw [he,Complex.normSq_zero] at hx
    norm_num at hx
  exact active_column_opposition _ _ _ _ _ _ ha hb hs
    (physical_reciprocal c d hc hd hkl j) (physical_sync c d hc hd hkl i j)
end Orbit37

end
end MainTheory.OrderFiveGridRemainingDisplays
