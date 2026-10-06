import MainTheory.Orbit12AnchorLines
import MainTheory.RankOneSpinorFrame
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit12EdgeLines
open scoped Matrix BigOperators
open SixQubit SixQubit.Orbit12 MainTheory.Orbit12Frames
open MainTheory.Orbit12PhysicalRowData MainTheory.Orbit12MomentDisplays
open MainTheory.Orbit6SpinorDisplays MainTheory.Orbit6LineCompletion
noncomputable section

def H1bottomFrame (c : SS.State 6 ℂ) := ∑ e : Fin 6,outer (a c e)
def H1topFrame (d : SS.State 6 ℂ) := outer (ut d)+outer (vt d)

theorem physical_H1_frame (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : H1bottomFrame c=H1topFrame d := by
  have hm := physical_moments c d hc hd hnc hnd hkl
  obtain ⟨r0,r1,r2,r3,roff,r5,r6,rdiag0,rdiag1,r9,r10,r11,r12,r13,r14,r15⟩ :=
    physical_row_data c d hc hd hnc hnd hkl
  have hd0 := SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl efA w0 (by decide)
  have hd5 := SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl efA w5 (by decide)
  change diagBot c efA w0=diagTop d efA w0 at hd0
  change diagBot c efA w5=diagTop d efA w5 at hd5
  rw [dexB_w0,dexT_w0] at hd0
  rw [dexB_w5,dexT_w5] at hd5
  have hall : star (c y8)*c y0+star (c y9)*c y1+star (c y10)*c y2+star (c y11)*c y3+star (c y12)*c y4+star (c y13)*c y5+star (c y14)*c y6+star (c y15)*c y7=star (d z8)*d z0+star (d z9)*d z1+star (d z10)*d z2+star (d z11)*d z3+star (d z12)*d z4+star (d z13)*d z5+star (d z14)*d z6+star (d z15)*d z7 := by
    linear_combination (1/2 : ℂ)*hd0+(1/2 : ℂ)*hd5
  have hedge : star (c y14)*c y6+star (c y13)*c y5+star (c y12)*c y4+
      star (c y11)*c y3+star (c y10)*c y2+star (c y9)*c y1=
      star (d z8)*d z0+star (d z15)*d z7 := by
    linear_combination hall-roff
  have hconj := congrArg star hedge
  simp only [star_add,star_mul',star_star] at hconj
  have hn0 := hm.n0
  have hn1 := hm.n1
  have hm1 := hm.m1
  change Complex.normSq (c y0)+Complex.normSq (c y1)+Complex.normSq (c y2)+Complex.normSq (c y3)+Complex.normSq (c y4)+Complex.normSq (c y5)+Complex.normSq (c y6)+Complex.normSq (c y7)+Complex.normSq (c y8)+Complex.normSq (c y9)+Complex.normSq (c y10)+Complex.normSq (c y11)+Complex.normSq (c y12)+Complex.normSq (c y13)+Complex.normSq (c y14)+Complex.normSq (c y15)=1 at hn0
  change Complex.normSq (d z0)+Complex.normSq (d z1)+Complex.normSq (d z2)+Complex.normSq (d z3)+Complex.normSq (d z4)+Complex.normSq (d z5)+Complex.normSq (d z6)+Complex.normSq (d z7)+Complex.normSq (d z8)+Complex.normSq (d z9)+Complex.normSq (d z10)+Complex.normSq (d z11)+Complex.normSq (d z12)+Complex.normSq (d z13)+Complex.normSq (d z14)+Complex.normSq (d z15)=1 at hn1
  change Complex.normSq (c y8)+Complex.normSq (c y9)+Complex.normSq (c y10)+Complex.normSq (c y11)+Complex.normSq (c y12)+Complex.normSq (c y13)+Complex.normSq (c y14)+Complex.normSq (c y15)=Complex.normSq (d z8)+Complex.normSq (d z9)+Complex.normSq (d z10)+Complex.normSq (d z11)+Complex.normSq (d z12)+Complex.normSq (d z13)+Complex.normSq (d z14)+Complex.normSq (d z15) at hm1
  have hlo : Complex.normSq (c y0)+Complex.normSq (c y1)+Complex.normSq (c y2)+Complex.normSq (c y3)+Complex.normSq (c y4)+Complex.normSq (c y5)+Complex.normSq (c y6)+Complex.normSq (c y7)=Complex.normSq (d z0)+Complex.normSq (d z1)+Complex.normSq (d z2)+Complex.normSq (d z3)+Complex.normSq (d z4)+Complex.normSq (d z5)+Complex.normSq (d z6)+Complex.normSq (d z7) := by
    linear_combination hn0-hn1-hm1
  have hhi : Complex.normSq (c y8)+Complex.normSq (c y9)+Complex.normSq (c y10)+Complex.normSq (c y11)+Complex.normSq (c y12)+Complex.normSq (c y13)+Complex.normSq (c y14)+Complex.normSq (c y15)=Complex.normSq (d z8)+Complex.normSq (d z9)+Complex.normSq (d z10)+Complex.normSq (d z11)+Complex.normSq (d z12)+Complex.normSq (d z13)+Complex.normSq (d z14)+Complex.normSq (d z15) := by
    linear_combination hm1
  have c0 := congrArg (fun x : ℝ => (x : ℂ)) hlo
  have c1 := congrArg (fun x : ℝ => (x : ℂ)) hhi
  have d0 := congrArg (fun x : ℝ => (x : ℂ)) rdiag0
  have d1 := congrArg (fun x : ℝ => (x : ℂ)) rdiag1
  push_cast at c0 c1 d0 d1
  simp only [Complex.normSq_eq_conj_mul_self] at c0 c1 d0 d1
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [H1bottomFrame,H1topFrame,outer,Matrix.sum_apply,Matrix.add_apply,Matrix.vecMulVec_apply,Pi.star_apply,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
  · change c y6*star (c y6)+(c y5*star (c y5)+(c y4*star (c y4)+(c y3*star (c y3)+(c y2*star (c y2)+(c y1*star (c y1))))))=d z0*star (d z0)+d z7*star (d z7)
    simp only [← Complex.star_def] at c0 c1 d0 d1 hedge hconj
    linear_combination c0-d0
  · change c y6*star (c y14)+(c y5*star (c y13)+(c y4*star (c y12)+(c y3*star (c y11)+(c y2*star (c y10)+(c y1*star (c y9))))))=d z0*star (d z8)+d z7*star (d z15)
    simp only [← Complex.star_def] at c0 c1 d0 d1 hedge hconj
    linear_combination hedge
  · change c y14*star (c y6)+(c y13*star (c y5)+(c y12*star (c y4)+(c y11*star (c y3)+(c y10*star (c y2)+(c y9*star (c y1))))))=d z8*star (d z0)+d z15*star (d z7)
    simp only [← Complex.star_def] at c0 c1 d0 d1 hedge hconj
    linear_combination hconj
  · change c y14*star (c y14)+(c y13*star (c y13)+(c y12*star (c y12)+(c y11*star (c y11)+(c y10*star (c y10)+(c y9*star (c y9))))))=d z8*star (d z8)+d z15*star (d z15)
    simp only [← Complex.star_def] at c0 c1 d0 d1 hedge hconj
    linear_combination c1-d1


theorem actual_edge_lines (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∀ e : Fin 6,∃ t : ℂ,b d e=t • u c) ∧
    (∀ e : Fin 6,∃ t : ℂ,a c e=t • ut d) := by
  obtain ⟨⟨t,ht⟩,⟨s,hs⟩⟩ := MainTheory.Orbit12AnchorLines.actual_anchor_lines
    c d hc hd hnc hnd hkl
  have hu := bottom_zero_anchor _ _ (physical_moments c d hc hd hnc hnd hkl)
  have hU := top_zero_anchor _ _ (physical_moments c d hc hd hnc hnd hkl)
  have hun : u c≠0 := by
    intro hz
    have h0 := congrFun hz 0
    have h1 := congrFun hz 1
    change c y0=0 at h0
    change c y8=0 at h1
    change Complex.normSq (c y0)+Complex.normSq (c y8)=1/4 at hu
    norm_num [h0,h1] at hu
  have hUn : ut d≠0 := by
    intro hz
    have h0 := congrFun hz 0
    have h1 := congrFun hz 1
    change d z0=0 at h0
    change d z8=0 at h1
    change Complex.normSq (d z0)+Complex.normSq (d z8)=1/4 at hU
    norm_num [h0,h1] at hU
  have hw : wedge (u c) (v c)=0 := by
    rw [ht]
    simp only [wedge,Pi.smul_apply,smul_eq_mul]
    ring
  have hW : wedge (ut d) (vt d)=0 := by
    rw [hs]
    simp only [wedge,Pi.smul_apply,smul_eq_mul]
    ring
  have hb := (physical_blocks c d hc hd hnc hnd hkl).2
  have ha := physical_H1_frame c d hc hd hnc hnd hkl
  have hwb := MainTheory.RankOneSpinorFrame.frame_wedges_zero (u c) (v c) (b d) hb hw
  have hwa := MainTheory.RankOneSpinorFrame.frame_wedges_zero (ut d) (vt d) (a c) ha.symm hW
  exact ⟨fun e => wedge_zero_scalar _ _ hun (hwb e),
    fun e => wedge_zero_scalar _ _ hUn (hwa e)⟩

end
end MainTheory.Orbit12EdgeLines
