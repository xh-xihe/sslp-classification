import MainTheory.Orbit12ScalarCompletion
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit12PairCompletion
open scoped Matrix BigOperators
open SixQubit SixQubit.Orbit12 MainTheory.Orbit12Frames MainTheory.Orbit12MomentDisplays
open MainTheory.Orbit12PhysicalRowData MainTheory.Orbit12AnchorScalars
open MainTheory.Orbit12ScalarCompletion
open MainTheory.Orbit6SpinorDisplays MainTheory.Orbit6LineCompletion
noncomputable section

def complementEdge (e : Fin 6) : Fin 6 := ⟨5-e.val,by omega⟩
theorem actual_complement_edges : ∀ e : Fin 6,∀ j : Fin 4,
    (j=(edges e).1 ∨ j=(edges e).2) ↔
      ¬(j=(edges (complementEdge e)).1 ∨ j=(edges (complementEdge e)).2) := by decide +kernel

theorem physical_pair_0 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    pairing (a c 0) (ut d)+pairing (v c) (b d 5)=0 ∧
    pairing (u c) (b d 5)+pairing (a c 0) (vt d)=0 := by
  have hp0 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w0 (by decide)
  change offSum c d ef2 w0=0 at hp0
  rw [ex_ef2_w0] at hp0
  have hp1 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w4 (by decide)
  change offSum c d ef2 w4=0 at hp1
  rw [ex_ef2_w4] at hp1
  have hq0 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w0 (by decide)
  change offSum c d ef3 w0=0 at hq0
  rw [ex_ef3_w0] at hq0
  have hq1 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w2 (by decide)
  change offSum c d ef3 w2=0 at hq1
  rw [ex_ef3_w2] at hq1
  constructor
  · change star (c y6)*d z0+star (c y14)*d z8+
      (star (c y7)*d z1+star (c y15)*d z9)=0
    linear_combination (1/2 : ℂ)*hp0+(1/2 : ℂ)*hp1
  · change star (c y0)*d z1+star (c y8)*d z9+
      (star (c y6)*d z7+star (c y14)*d z15)=0
    linear_combination (1/2 : ℂ)*hq0-(1/2 : ℂ)*hq1

theorem physical_pair_1 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    pairing (a c 1) (ut d)+pairing (v c) (b d 4)=0 ∧
    pairing (u c) (b d 4)+pairing (a c 1) (vt d)=0 := by
  have hp0 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w0 (by decide)
  change offSum c d ef4 w0=0 at hp0
  rw [ex_ef4_w0] at hp0
  have hp1 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w3 (by decide)
  change offSum c d ef4 w3=0 at hp1
  rw [ex_ef4_w3] at hp1
  have hq0 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef5 w0 (by decide)
  change offSum c d ef5 w0=0 at hq0
  rw [ex_ef5_w0] at hq0
  have hq1 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef5 w2 (by decide)
  change offSum c d ef5 w2=0 at hq1
  rw [ex_ef5_w2] at hq1
  constructor
  · change star (c y5)*d z0+star (c y13)*d z8+
      (star (c y7)*d z2+star (c y15)*d z10)=0
    linear_combination (1/2 : ℂ)*hp0+(1/2 : ℂ)*hp1
  · change star (c y0)*d z2+star (c y8)*d z10+
      (star (c y5)*d z7+star (c y13)*d z15)=0
    linear_combination (1/2 : ℂ)*hq0-(1/2 : ℂ)*hq1

theorem physical_pair_2 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    pairing (a c 2) (ut d)+pairing (v c) (b d 3)=0 ∧
    pairing (u c) (b d 3)+pairing (a c 2) (vt d)=0 := by
  have hp0 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef6 w0 (by decide)
  change offSum c d ef6 w0=0 at hp0
  rw [ex_ef6_w0] at hp0
  have hp1 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef6 w2 (by decide)
  change offSum c d ef6 w2=0 at hp1
  rw [ex_ef6_w2] at hp1
  have hq0 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef7 w0 (by decide)
  change offSum c d ef7 w0=0 at hq0
  rw [ex_ef7_w0] at hq0
  have hq1 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef7 w3 (by decide)
  change offSum c d ef7 w3=0 at hq1
  rw [ex_ef7_w3] at hq1
  constructor
  · change star (c y4)*d z0+star (c y12)*d z8+
      (star (c y7)*d z3+star (c y15)*d z11)=0
    linear_combination (1/2 : ℂ)*hp0+(1/2 : ℂ)*hp1
  · change star (c y0)*d z3+star (c y8)*d z11+
      (star (c y4)*d z7+star (c y12)*d z15)=0
    linear_combination (1/2 : ℂ)*hq0-(1/2 : ℂ)*hq1

theorem physical_pair_3 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    pairing (a c 3) (ut d)+pairing (v c) (b d 2)=0 ∧
    pairing (u c) (b d 2)+pairing (a c 3) (vt d)=0 := by
  have hp0 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef7 w0 (by decide)
  change offSum c d ef7 w0=0 at hp0
  rw [ex_ef7_w0] at hp0
  have hp1 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef7 w3 (by decide)
  change offSum c d ef7 w3=0 at hp1
  rw [ex_ef7_w3] at hp1
  have hq0 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef6 w0 (by decide)
  change offSum c d ef6 w0=0 at hq0
  rw [ex_ef6_w0] at hq0
  have hq1 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef6 w2 (by decide)
  change offSum c d ef6 w2=0 at hq1
  rw [ex_ef6_w2] at hq1
  constructor
  · change star (c y3)*d z0+star (c y11)*d z8+
      (star (c y7)*d z4+star (c y15)*d z12)=0
    linear_combination (1/2 : ℂ)*hp0+(1/2 : ℂ)*hp1
  · change star (c y0)*d z4+star (c y8)*d z12+
      (star (c y3)*d z7+star (c y11)*d z15)=0
    linear_combination (1/2 : ℂ)*hq0-(1/2 : ℂ)*hq1

theorem physical_pair_4 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    pairing (a c 4) (ut d)+pairing (v c) (b d 1)=0 ∧
    pairing (u c) (b d 1)+pairing (a c 4) (vt d)=0 := by
  have hp0 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef5 w0 (by decide)
  change offSum c d ef5 w0=0 at hp0
  rw [ex_ef5_w0] at hp0
  have hp1 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef5 w2 (by decide)
  change offSum c d ef5 w2=0 at hp1
  rw [ex_ef5_w2] at hp1
  have hq0 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w0 (by decide)
  change offSum c d ef4 w0=0 at hq0
  rw [ex_ef4_w0] at hq0
  have hq1 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w3 (by decide)
  change offSum c d ef4 w3=0 at hq1
  rw [ex_ef4_w3] at hq1
  constructor
  · change star (c y2)*d z0+star (c y10)*d z8+
      (star (c y7)*d z5+star (c y15)*d z13)=0
    linear_combination (1/2 : ℂ)*hp0+(1/2 : ℂ)*hp1
  · change star (c y0)*d z5+star (c y8)*d z13+
      (star (c y2)*d z7+star (c y10)*d z15)=0
    linear_combination (1/2 : ℂ)*hq0-(1/2 : ℂ)*hq1

theorem physical_pair_5 (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    pairing (a c 5) (ut d)+pairing (v c) (b d 0)=0 ∧
    pairing (u c) (b d 0)+pairing (a c 5) (vt d)=0 := by
  have hp0 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w0 (by decide)
  change offSum c d ef3 w0=0 at hp0
  rw [ex_ef3_w0] at hp0
  have hp1 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w2 (by decide)
  change offSum c d ef3 w2=0 at hp1
  rw [ex_ef3_w2] at hp1
  have hq0 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w0 (by decide)
  change offSum c d ef2 w0=0 at hq0
  rw [ex_ef2_w0] at hq0
  have hq1 := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w4 (by decide)
  change offSum c d ef2 w4=0 at hq1
  rw [ex_ef2_w4] at hq1
  constructor
  · change star (c y1)*d z0+star (c y9)*d z8+
      (star (c y7)*d z6+star (c y15)*d z14)=0
    linear_combination (1/2 : ℂ)*hp0+(1/2 : ℂ)*hp1
  · change star (c y0)*d z6+star (c y8)*d z14+
      (star (c y1)*d z7+star (c y9)*d z15)=0
    linear_combination (1/2 : ℂ)*hq0-(1/2 : ℂ)*hq1

theorem actual_pair_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (e : Fin 6) :
    pairing (a c e) (ut d)+pairing (v c) (b d (complementEdge e))=0 ∧
    pairing (u c) (b d (complementEdge e))+pairing (a c e) (vt d)=0 := by
  fin_cases e
  · exact physical_pair_0 c d hc hd hkl
  · exact physical_pair_1 c d hc hd hkl
  · exact physical_pair_2 c d hc hd hkl
  · exact physical_pair_3 c d hc hd hkl
  · exact physical_pair_4 c d hc hd hkl
  · exact physical_pair_5 c d hc hd hkl

theorem actual_scalar_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3)
    (alpha0 alpha4 beta0 beta4 : ℂ) (A B : Fin 6 → ℂ)
    (hs : ScalarData c d alpha0 alpha4 beta0 beta4 A B) (e : Fin 6) :
    (star (A e)*beta0+star alpha4*B (complementEdge e)=0) ∧
    (star alpha0*B (complementEdge e)+star (A e)*beta4=0) := by
  obtain ⟨hL,hM,hu,hv,hU,hV,ha,hb⟩ := hs
  obtain ⟨h1,h2⟩ := actual_pair_rows c d hc hd hkl e
  simp only [hu,hv,hU,hV,ha e,hb (complementEdge e)] at h1 h2
  exact pair_scalar_rows _ _ _ _ _ _ _ _ hL hM h1 h2

theorem actual_eliminated_anchor_equality (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3)
    (alpha0 alpha4 beta0 beta4 : ℂ) (A B : Fin 6 → ℂ)
    (hs : ScalarData c d alpha0 alpha4 beta0 beta4 A B)
    (e : Fin 6) (hp : 0<nsq (a c e)) :
    beta0*star alpha0=beta4*star alpha4 := by
  obtain ⟨h1,h2⟩ := actual_scalar_rows c d hc hd hkl _ _ _ _ A B hs e
  have ha := hs.2.2.2.2.2.2.1 e
  have hA : A e≠0 := by
    intro hz
    rw [ha,hz,zero_smul] at hp
    norm_num [nsq] at hp
  exact eliminated_anchor_equality _ _ _ _ _ _ hA h1 h2

end
end MainTheory.Orbit12PairCompletion
