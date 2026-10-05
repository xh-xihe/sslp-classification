import MainTheory.Orbit30ProbabilityLabels
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit30PhysicalRows
open SixQubit.Orbit30
open MainTheory.Orbit30PrintedMoments MainTheory.Orbit30ProbabilityLabels
noncomputable section
def pointC (c : SS.State 6 ℂ) (i : Fin 5) : ℂ := c (bottom (vertexIndex i))
def pointV (d : SS.State 6 ℂ) (i : Fin 5) : ℂ := d (top (complementIndex (vertexIndex i)))
def edgeIndexMatrix : Fin 5 → Fin 5 → Fin 16 := ![![⟨0,by decide⟩,⟨14,by decide⟩,⟨13,by decide⟩,⟨11,by decide⟩,⟨7,by decide⟩],![⟨14,by decide⟩,⟨0,by decide⟩,⟨12,by decide⟩,⟨10,by decide⟩,⟨6,by decide⟩],![⟨13,by decide⟩,⟨12,by decide⟩,⟨0,by decide⟩,⟨9,by decide⟩,⟨5,by decide⟩],![⟨11,by decide⟩,⟨10,by decide⟩,⟨9,by decide⟩,⟨0,by decide⟩,⟨3,by decide⟩],![⟨7,by decide⟩,⟨6,by decide⟩,⟨5,by decide⟩,⟨3,by decide⟩,⟨0,by decide⟩]]
def edgeC (c : SS.State 6 ℂ) (i j : Fin 5) : ℂ :=
  if i=j then 0 else c (bottom (edgeIndexMatrix i j))
def edgeV (d : SS.State 6 ℂ) (i j : Fin 5) : ℂ :=
  if i=j then 0 else d (top (complementIndex (edgeIndexMatrix i j)))
def pointU (c : SS.State 6 ℂ) (i : Fin 5) : ℂ := star (pointC c i)
def edgeU (c : SS.State 6 ℂ) (i j : Fin 5) : ℂ := star (edgeC c i j)
def anchorU (c : SS.State 6 ℂ) : ℂ := star (c y15)
def anchorV (d : SS.State 6 ℂ) : ℂ := d z0
def starSum (c d : SS.State 6 ℂ) : Fin 5 → ℂ := ![pointU c ⟨1,by decide⟩*edgeV d ⟨0,by decide⟩ ⟨1,by decide⟩ + pointU c ⟨2,by decide⟩*edgeV d ⟨0,by decide⟩ ⟨2,by decide⟩ + pointU c ⟨3,by decide⟩*edgeV d ⟨0,by decide⟩ ⟨3,by decide⟩ + pointU c ⟨4,by decide⟩*edgeV d ⟨0,by decide⟩ ⟨4,by decide⟩,pointU c ⟨0,by decide⟩*edgeV d ⟨1,by decide⟩ ⟨0,by decide⟩ + pointU c ⟨2,by decide⟩*edgeV d ⟨1,by decide⟩ ⟨2,by decide⟩ + pointU c ⟨3,by decide⟩*edgeV d ⟨1,by decide⟩ ⟨3,by decide⟩ + pointU c ⟨4,by decide⟩*edgeV d ⟨1,by decide⟩ ⟨4,by decide⟩,pointU c ⟨0,by decide⟩*edgeV d ⟨2,by decide⟩ ⟨0,by decide⟩ + pointU c ⟨1,by decide⟩*edgeV d ⟨2,by decide⟩ ⟨1,by decide⟩ + pointU c ⟨3,by decide⟩*edgeV d ⟨2,by decide⟩ ⟨3,by decide⟩ + pointU c ⟨4,by decide⟩*edgeV d ⟨2,by decide⟩ ⟨4,by decide⟩,pointU c ⟨0,by decide⟩*edgeV d ⟨3,by decide⟩ ⟨0,by decide⟩ + pointU c ⟨1,by decide⟩*edgeV d ⟨3,by decide⟩ ⟨1,by decide⟩ + pointU c ⟨2,by decide⟩*edgeV d ⟨3,by decide⟩ ⟨2,by decide⟩ + pointU c ⟨4,by decide⟩*edgeV d ⟨3,by decide⟩ ⟨4,by decide⟩,pointU c ⟨0,by decide⟩*edgeV d ⟨4,by decide⟩ ⟨0,by decide⟩ + pointU c ⟨1,by decide⟩*edgeV d ⟨4,by decide⟩ ⟨1,by decide⟩ + pointU c ⟨2,by decide⟩*edgeV d ⟨4,by decide⟩ ⟨2,by decide⟩ + pointU c ⟨3,by decide⟩*edgeV d ⟨4,by decide⟩ ⟨3,by decide⟩]
def matchingSum (c d : SS.State 6 ℂ) : Fin 5 → ℂ := ![edgeU c ⟨1,by decide⟩ ⟨2,by decide⟩*edgeV d ⟨3,by decide⟩ ⟨4,by decide⟩ + edgeU c ⟨3,by decide⟩ ⟨4,by decide⟩*edgeV d ⟨1,by decide⟩ ⟨2,by decide⟩ + edgeU c ⟨1,by decide⟩ ⟨3,by decide⟩*edgeV d ⟨2,by decide⟩ ⟨4,by decide⟩ + edgeU c ⟨2,by decide⟩ ⟨4,by decide⟩*edgeV d ⟨1,by decide⟩ ⟨3,by decide⟩ + edgeU c ⟨1,by decide⟩ ⟨4,by decide⟩*edgeV d ⟨2,by decide⟩ ⟨3,by decide⟩ + edgeU c ⟨2,by decide⟩ ⟨3,by decide⟩*edgeV d ⟨1,by decide⟩ ⟨4,by decide⟩,edgeU c ⟨0,by decide⟩ ⟨2,by decide⟩*edgeV d ⟨3,by decide⟩ ⟨4,by decide⟩ + edgeU c ⟨3,by decide⟩ ⟨4,by decide⟩*edgeV d ⟨0,by decide⟩ ⟨2,by decide⟩ + edgeU c ⟨0,by decide⟩ ⟨3,by decide⟩*edgeV d ⟨2,by decide⟩ ⟨4,by decide⟩ + edgeU c ⟨2,by decide⟩ ⟨4,by decide⟩*edgeV d ⟨0,by decide⟩ ⟨3,by decide⟩ + edgeU c ⟨0,by decide⟩ ⟨4,by decide⟩*edgeV d ⟨2,by decide⟩ ⟨3,by decide⟩ + edgeU c ⟨2,by decide⟩ ⟨3,by decide⟩*edgeV d ⟨0,by decide⟩ ⟨4,by decide⟩,edgeU c ⟨0,by decide⟩ ⟨1,by decide⟩*edgeV d ⟨3,by decide⟩ ⟨4,by decide⟩ + edgeU c ⟨3,by decide⟩ ⟨4,by decide⟩*edgeV d ⟨0,by decide⟩ ⟨1,by decide⟩ + edgeU c ⟨0,by decide⟩ ⟨3,by decide⟩*edgeV d ⟨1,by decide⟩ ⟨4,by decide⟩ + edgeU c ⟨1,by decide⟩ ⟨4,by decide⟩*edgeV d ⟨0,by decide⟩ ⟨3,by decide⟩ + edgeU c ⟨0,by decide⟩ ⟨4,by decide⟩*edgeV d ⟨1,by decide⟩ ⟨3,by decide⟩ + edgeU c ⟨1,by decide⟩ ⟨3,by decide⟩*edgeV d ⟨0,by decide⟩ ⟨4,by decide⟩,edgeU c ⟨0,by decide⟩ ⟨1,by decide⟩*edgeV d ⟨2,by decide⟩ ⟨4,by decide⟩ + edgeU c ⟨2,by decide⟩ ⟨4,by decide⟩*edgeV d ⟨0,by decide⟩ ⟨1,by decide⟩ + edgeU c ⟨0,by decide⟩ ⟨2,by decide⟩*edgeV d ⟨1,by decide⟩ ⟨4,by decide⟩ + edgeU c ⟨1,by decide⟩ ⟨4,by decide⟩*edgeV d ⟨0,by decide⟩ ⟨2,by decide⟩ + edgeU c ⟨0,by decide⟩ ⟨4,by decide⟩*edgeV d ⟨1,by decide⟩ ⟨2,by decide⟩ + edgeU c ⟨1,by decide⟩ ⟨2,by decide⟩*edgeV d ⟨0,by decide⟩ ⟨4,by decide⟩,edgeU c ⟨0,by decide⟩ ⟨1,by decide⟩*edgeV d ⟨2,by decide⟩ ⟨3,by decide⟩ + edgeU c ⟨2,by decide⟩ ⟨3,by decide⟩*edgeV d ⟨0,by decide⟩ ⟨1,by decide⟩ + edgeU c ⟨0,by decide⟩ ⟨2,by decide⟩*edgeV d ⟨1,by decide⟩ ⟨3,by decide⟩ + edgeU c ⟨1,by decide⟩ ⟨3,by decide⟩*edgeV d ⟨0,by decide⟩ ⟨2,by decide⟩ + edgeU c ⟨0,by decide⟩ ⟨3,by decide⟩*edgeV d ⟨1,by decide⟩ ⟨2,by decide⟩ + edgeU c ⟨1,by decide⟩ ⟨2,by decide⟩*edgeV d ⟨0,by decide⟩ ⟨3,by decide⟩]
def NativeRows (c d : SS.State 6 ℂ) : Prop :=
    star (c y1) * d z1 - star (c y14) * d z14 = 0
      ∧ star (c y2) * d z2 - star (c y13) * d z13 = 0
      ∧ star (c y4) * d z4 - star (c y11) * d z11 = 0
      ∧ star (c y8) * d z8 - star (c y7) * d z7 = 0
      ∧ star (c y0) * d z1 - star (c y14) * d z15 = 0
      ∧ star (c y2) * d z3 - star (c y12) * d z13 = 0
      ∧ star (c y4) * d z5 - star (c y10) * d z11 = 0
      ∧ star (c y8) * d z9 - star (c y6) * d z7 = 0
      ∧ star (c y0) * d z2 - star (c y13) * d z15 = 0
      ∧ star (c y1) * d z3 - star (c y12) * d z14 = 0
      ∧ star (c y4) * d z6 - star (c y9) * d z11 = 0
      ∧ star (c y8) * d z10 - star (c y5) * d z7 = 0
      ∧ star (c y0) * d z4 - star (c y11) * d z15 = 0
      ∧ star (c y1) * d z5 - star (c y10) * d z14 = 0
      ∧ star (c y2) * d z6 - star (c y9) * d z13 = 0
      ∧ star (c y8) * d z12 - star (c y3) * d z7 = 0
      ∧ star (c y0) * d z8 - star (c y7) * d z15 = 0
      ∧ star (c y1) * d z9 - star (c y6) * d z14 = 0
      ∧ star (c y2) * d z10 - star (c y5) * d z13 = 0
      ∧ star (c y4) * d z12 - star (c y3) * d z11 = 0
      ∧ star (c y12) * d z12 + star (c y3) * d z3 + star (c y10) * d z10 + star (c y5) * d z5 + star (c y6) * d z6 + star (c y9) * d z9 = 0
      ∧ star (c y13) * d z12 + star (c y3) * d z2 + star (c y11) * d z10 + star (c y5) * d z4 + star (c y7) * d z6 + star (c y9) * d z8 = 0
      ∧ star (c y14) * d z12 + star (c y3) * d z1 + star (c y11) * d z9 + star (c y6) * d z4 + star (c y7) * d z5 + star (c y10) * d z8 = 0
      ∧ star (c y14) * d z10 + star (c y5) * d z1 + star (c y13) * d z9 + star (c y6) * d z2 + star (c y7) * d z3 + star (c y12) * d z8 = 0
      ∧ star (c y14) * d z6 + star (c y9) * d z1 + star (c y13) * d z5 + star (c y10) * d z2 + star (c y11) * d z3 + star (c y12) * d z4 = 0
      ∧ star (c y15) * d z15 + star (c y0) * d z0 = 0
      ∧ star (c y15) * d z14 + star (c y1) * d z0 = 0
      ∧ star (c y15) * d z13 + star (c y2) * d z0 = 0
      ∧ star (c y15) * d z11 + star (c y4) * d z0 = 0
      ∧ star (c y15) * d z7 + star (c y8) * d z0 = 0
      ∧ star (c y1) * d z1 + star (c y2) * d z2 + star (c y4) * d z4 + star (c y8) * d z8 = 0
      ∧ star (c y0) * d z1 + star (c y2) * d z3 + star (c y4) * d z5 + star (c y8) * d z9 = 0
      ∧ star (c y0) * d z2 + star (c y1) * d z3 + star (c y4) * d z6 + star (c y8) * d z10 = 0
      ∧ star (c y0) * d z4 + star (c y1) * d z5 + star (c y2) * d z6 + star (c y8) * d z12 = 0
      ∧ star (c y0) * d z8 + star (c y1) * d z9 + star (c y2) * d z10 + star (c y4) * d z12 = 0
theorem physical_native_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : NativeRows c d := by
  exact SixQubit.Orbit30.rows c d
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef0 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef0 w2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef0 w3 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef0 w4 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef0 w5 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef1 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef1 w2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w4 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef2 w5 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef3 w2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w3 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef4 w5 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef5 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef5 w2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef6 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef6 w1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef6 w2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef6 w3 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef6 w4 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef7 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef7 w2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef8 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef8 w1 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef8 w2 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef8 w3 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef8 w4 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef9 w0 (by decide))
    (SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl ef9 w2 (by decide))
theorem canonical_rows (c d : SS.State 6 ℂ) (h : NativeRows c d) :
    (∀ i j,i≠j → pointU c j*edgeV d i j-edgeU c i j*pointV d j=0) ∧
    (∀ i,anchorU c*pointV d i+pointU c i*anchorV d=0) ∧
    (∀ i,starSum c d i=0) ∧ (∀ i,matchingSum c d i=0) := by
  rcases h with ⟨D0_1,D0_2,D0_3,D0_4,D1_0,D1_2,D1_3,D1_4,D2_0,D2_1,D2_3,D2_4,D3_0,D3_1,D3_2,D3_4,D4_0,D4_1,D4_2,D4_3,M0,M1,M2,M3,M4,R0,R1,R2,R3,R4,T0,T1,T2,T3,T4⟩
  refine ⟨?_,?_,?_,?_⟩
  · intro i j hi
    fin_cases i <;> fin_cases j
    · exact False.elim (hi rfl)
    · change star (c y1)*d z1-star (c y14)*d z14=0
      exact D0_1
    · change star (c y2)*d z2-star (c y13)*d z13=0
      exact D0_2
    · change star (c y4)*d z4-star (c y11)*d z11=0
      exact D0_3
    · change star (c y8)*d z8-star (c y7)*d z7=0
      exact D0_4
    · change star (c y0)*d z1-star (c y14)*d z15=0
      exact D1_0
    · exact False.elim (hi rfl)
    · change star (c y2)*d z3-star (c y12)*d z13=0
      exact D1_2
    · change star (c y4)*d z5-star (c y10)*d z11=0
      exact D1_3
    · change star (c y8)*d z9-star (c y6)*d z7=0
      exact D1_4
    · change star (c y0)*d z2-star (c y13)*d z15=0
      exact D2_0
    · change star (c y1)*d z3-star (c y12)*d z14=0
      exact D2_1
    · exact False.elim (hi rfl)
    · change star (c y4)*d z6-star (c y9)*d z11=0
      exact D2_3
    · change star (c y8)*d z10-star (c y5)*d z7=0
      exact D2_4
    · change star (c y0)*d z4-star (c y11)*d z15=0
      exact D3_0
    · change star (c y1)*d z5-star (c y10)*d z14=0
      exact D3_1
    · change star (c y2)*d z6-star (c y9)*d z13=0
      exact D3_2
    · exact False.elim (hi rfl)
    · change star (c y8)*d z12-star (c y3)*d z7=0
      exact D3_4
    · change star (c y0)*d z8-star (c y7)*d z15=0
      exact D4_0
    · change star (c y1)*d z9-star (c y6)*d z14=0
      exact D4_1
    · change star (c y2)*d z10-star (c y5)*d z13=0
      exact D4_2
    · change star (c y4)*d z12-star (c y3)*d z11=0
      exact D4_3
    · exact False.elim (hi rfl)
  · intro i
    fin_cases i
    · change star (c y15)*d z15+star (c y0)*d z0=0
      exact R0
    · change star (c y15)*d z14+star (c y1)*d z0=0
      exact R1
    · change star (c y15)*d z13+star (c y2)*d z0=0
      exact R2
    · change star (c y15)*d z11+star (c y4)*d z0=0
      exact R3
    · change star (c y15)*d z7+star (c y8)*d z0=0
      exact R4
  · intro i
    fin_cases i
    · change star (c y1)*d z1 + star (c y2)*d z2 + star (c y4)*d z4 + star (c y8)*d z8=0
      exact T0
    · change star (c y0)*d z1 + star (c y2)*d z3 + star (c y4)*d z5 + star (c y8)*d z9=0
      exact T1
    · change star (c y0)*d z2 + star (c y1)*d z3 + star (c y4)*d z6 + star (c y8)*d z10=0
      exact T2
    · change star (c y0)*d z4 + star (c y1)*d z5 + star (c y2)*d z6 + star (c y8)*d z12=0
      exact T3
    · change star (c y0)*d z8 + star (c y1)*d z9 + star (c y2)*d z10 + star (c y4)*d z12=0
      exact T4
  · intro i
    fin_cases i
    · change star (c y12)*d z12 + star (c y3)*d z3 + star (c y10)*d z10 + star (c y5)*d z5 + star (c y6)*d z6 + star (c y9)*d z9=0
      exact M0
    · change star (c y13)*d z12 + star (c y3)*d z2 + star (c y11)*d z10 + star (c y5)*d z4 + star (c y7)*d z6 + star (c y9)*d z8=0
      exact M1
    · change star (c y14)*d z12 + star (c y3)*d z1 + star (c y11)*d z9 + star (c y6)*d z4 + star (c y7)*d z5 + star (c y10)*d z8=0
      exact M2
    · change star (c y14)*d z10 + star (c y5)*d z1 + star (c y13)*d z9 + star (c y6)*d z2 + star (c y7)*d z3 + star (c y12)*d z8=0
      exact M3
    · change star (c y14)*d z6 + star (c y9)*d z1 + star (c y13)*d z5 + star (c y10)*d z2 + star (c y11)*d z3 + star (c y12)*d z4=0
      exact M4
theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∀ i j,i≠j → pointU c j*edgeV d i j-edgeU c i j*pointV d j=0) ∧
    (∀ i,anchorU c*pointV d i+pointU c i*anchorV d=0) ∧
    (∀ i,starSum c d i=0) ∧ (∀ i,matchingSum c d i=0) :=
  canonical_rows c d (physical_native_rows c d hc hd hkl)
end
end MainTheory.Orbit30PhysicalRows
