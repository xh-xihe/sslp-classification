import MainTheory.Orbit45BottomGauge

/-! The literal top-fiber gauge follows from the actual half-angle rows,
matched probabilities and the physical relative logical phase. -/
set_option autoImplicit false
namespace MainTheory.Orbit45TopGauge
open MainTheory.Orbit45PrintedFibers MainTheory.Orbit45PhysicalPrintedRows
open MainTheory.Orbit45PhysicalGauge MainTheory.Orbit45PhysicalProbabilityDomain
noncomputable section

theorem top_norm (c d : SS.State 6 ℂ) (H : FullKL c d) (i : Fin 10)
    (r : ℝ) (hr : 0≤r) (hc : c (bottom i)=(r : ℂ)) : ‖d (top i)‖=r := by
  have he : Complex.normSq (d (top i))=Complex.normSq (c (bottom i)) :=
    (matching_probabilities c d H.support0 H.support1 H.norm0 H.norm1 H.distance i).symm
  rw [Complex.norm_def,he,← Complex.norm_def,hc,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]

theorem top_canonical (c d : SS.State 6 ℂ) (H : FullKL c d)
    (B G S h : ℝ) (U V W : ℂ)
    (hB : 0<B) (hG : 0<G) (hS : 0<S) (hh : 0<h) (hsq : h^2=1/8)
    (hC : (fun i => c (bottom i))=Orbit45CrossFactors.C B G S h U V W)
    (hz : z c d ⟨3,by decide⟩=1/8) :
    ∃ xi eta zeta : ℂ,
      Complex.normSq xi=1 ∧ Complex.normSq eta=1 ∧ Complex.normSq zeta=1 ∧
      (fun i => d (top i))=Orbit45CrossFactors.D B G S h U V W xi eta zeta := by
  have c0 := congrFun hC ⟨0,by decide⟩
  have c1 := congrFun hC ⟨1,by decide⟩
  have c2 := congrFun hC ⟨2,by decide⟩
  have c3 := congrFun hC ⟨3,by decide⟩
  have c4 := congrFun hC ⟨4,by decide⟩
  have c5 := congrFun hC ⟨5,by decide⟩
  have c6 := congrFun hC ⟨6,by decide⟩
  have c7 := congrFun hC ⟨7,by decide⟩
  have c8 := congrFun hC ⟨8,by decide⟩
  have c9 := congrFun hC ⟨9,by decide⟩
  norm_num [Orbit45CrossFactors.C] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9
  have b0 : (B : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  have g0 : (G : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hG
  have s0 : (S : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hS
  have h0 : (h : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hh
  have hs : (h : ℂ)*(h : ℂ)=1/8 := by
    have he : h*h=1/8 := by nlinarith only [hsq]
    rw [← Complex.ofReal_mul,he]
    norm_num
  let xi := Orbit45PrintedConsequences.unitPhase (d (top 1))
  let eta := Orbit45PrintedConsequences.unitPhase (d (top 0))
  let zeta := Orbit45PrintedConsequences.unitPhase (d (top ⟨2,by decide⟩))
  have d0 := Orbit45PrintedConsequences.unitPhase_value (d (top 0))
  have d1 := Orbit45PrintedConsequences.unitPhase_value (d (top 1))
  have d2 := Orbit45PrintedConsequences.unitPhase_value (d (top ⟨2,by decide⟩))
  rw [top_norm c d H 0 G hG.le c0] at d0
  rw [top_norm c d H 1 B hB.le c1] at d1
  rw [top_norm c d H ⟨2,by decide⟩ S hS.le c2] at d2
  have d3 : d (top ⟨3,by decide⟩)=(h : ℂ) := by
    change star (c (bottom ⟨3,by decide⟩))*d (top ⟨3,by decide⟩)=1/8 at hz
    rw [c3] at hz
    simp only [Complex.star_def,Complex.conj_ofReal] at hz
    exact (mul_left_cancel₀ h0) (hz.trans hs.symm)
  have kernel := physical_cross_kernel c d H.support0 H.support1 H.distance
  have k4 := congrFun kernel ⟨4,by decide⟩
  have k5 := congrFun kernel ⟨5,by decide⟩
  change z c d ⟨4,by decide⟩= -z c d ⟨3,by decide⟩ at k4
  change z c d ⟨5,by decide⟩= -z c d ⟨3,by decide⟩ at k5
  rw [hz] at k4 k5
  change star (c (bottom ⟨4,by decide⟩))*d (top ⟨4,by decide⟩)= -(1/8 : ℂ) at k4
  change star (c (bottom ⟨5,by decide⟩))*d (top ⟨5,by decide⟩)= -(1/8 : ℂ) at k5
  rw [c4] at k4
  rw [c5] at k5
  simp only [Complex.star_def,Complex.conj_ofReal] at k4 k5
  have d4 : d (top ⟨4,by decide⟩)= -(h : ℂ) := by
    apply mul_left_cancel₀ h0
    linear_combination k4+hs
  have d5 : d (top ⟨5,by decide⟩)= -(h : ℂ) := by
    apply mul_left_cancel₀ h0
    linear_combination k5+hs
  have a6 := physical_paired_products c d H.support0 H.support1 H.norm0 H.norm1 H.distance ⟨3,by decide⟩
  have a7 := physical_paired_products c d H.support0 H.support1 H.norm0 H.norm1 H.distance ⟨2,by decide⟩
  have a8 := physical_paired_products c d H.support0 H.support1 H.norm0 H.norm1 H.distance ⟨1,by decide⟩
  have a9 := physical_paired_products c d H.support0 H.support1 H.norm0 H.norm1 H.distance ⟨0,by decide⟩
  change c (bottom ⟨3,by decide⟩)*d (top ⟨6,by decide⟩)=c (bottom ⟨6,by decide⟩)*d (top ⟨3,by decide⟩) at a6
  change c (bottom ⟨2,by decide⟩)*d (top ⟨7,by decide⟩)=c (bottom ⟨7,by decide⟩)*d (top ⟨2,by decide⟩) at a7
  change c (bottom 1)*d (top ⟨8,by decide⟩)=c (bottom ⟨8,by decide⟩)*d (top 1) at a8
  change c (bottom 0)*d (top ⟨9,by decide⟩)=c (bottom ⟨9,by decide⟩)*d (top 0) at a9
  rw [c3,c6,d3] at a6
  rw [c2,c7,← d2] at a7
  rw [c1,c8,← d1] at a8
  rw [c0,c9,← d0] at a9
  have d6 : d (top ⟨6,by decide⟩)=(h : ℂ)*U := by
    apply mul_left_cancel₀ h0
    linear_combination a6
  have d7 : d (top ⟨7,by decide⟩)=(S : ℂ)*zeta := (mul_left_cancel₀ s0) a7
  have d8 : d (top ⟨8,by decide⟩)=(B : ℂ)*V*xi := by
    apply mul_left_cancel₀ b0
    linear_combination a8
  have d9 : d (top ⟨9,by decide⟩)=(G : ℂ)*W*eta := by
    apply mul_left_cancel₀ g0
    linear_combination a9
  refine ⟨xi,eta,zeta,Orbit45PrintedConsequences.unitPhase_normSq _,
    Orbit45PrintedConsequences.unitPhase_normSq _,Orbit45PrintedConsequences.unitPhase_normSq _,?_⟩
  funext i
  fin_cases i <;> norm_num only [Orbit45CrossFactors.D,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.mk_one,Fin.mk_zero] <;>
    first | exact d0.symm | exact d1.symm | exact d2.symm | exact d3 | exact d4 |
      exact d5 | exact d6 | exact d7 | exact d8 | exact d9
end
end MainTheory.Orbit45TopGauge
