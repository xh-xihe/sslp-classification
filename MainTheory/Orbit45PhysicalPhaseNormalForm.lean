import MainTheory.Orbit45TopGauge

/-! The complete preceding bottom and top gauges are available for every
actual positive-stratum code; neither displayed gauge is an assumption. -/
set_option autoImplicit false
namespace MainTheory.Orbit45PhysicalPhaseNormalForm
open MainTheory.Orbit45PrintedFibers MainTheory.Orbit45PhysicalPrintedRows
open MainTheory.Orbit45PhysicalGauge MainTheory.Orbit45AffineGauge
open MainTheory.Orbit45PhysicalProbabilityDomain
noncomputable section

theorem physical_phase_normal_form (c d : SS.State 6 ℂ) (H : FullKL c d)
    (hpos : 0<p c 1*p c 0*p c 2) :
    ∃ (theta : Fin 7 → ℝ) (tau U V W xi eta zeta : ℂ),
      let c' := phaseAction theta c
      let d' := tau • phaseAction theta d
      star tau*tau=1 ∧ FullKL c' d' ∧ p c'=p c ∧
      Complex.normSq U=1 ∧ Complex.normSq V=1 ∧ Complex.normSq W=1 ∧
      Complex.normSq xi=1 ∧ Complex.normSq eta=1 ∧ Complex.normSq zeta=1 ∧
      (fun i => c' (bottom i))=Orbit45CrossFactors.C
        (Real.sqrt (p c 1)) (Real.sqrt (p c 0)) (Real.sqrt (p c 2)) (1/Real.sqrt 8) U V W ∧
      (fun i => d' (top i))=Orbit45CrossFactors.D
        (Real.sqrt (p c 1)) (Real.sqrt (p c 0)) (Real.sqrt (p c 2)) (1/Real.sqrt 8) U V W xi eta zeta := by
  obtain ⟨theta,U,V,W,hH,hp,_,hU,hV,hW,hC⟩ := Orbit45BottomGauge.physical_bottom_gauge c d H
  let cg := phaseAction theta c
  let dg := phaseAction theta d
  let tau := Orbit45RelativeLogicalPhase.phase cg dg
  have htau : star tau*tau=1 := Orbit45RelativeLogicalPhase.phase_unit cg dg
    hH.support0 hH.support1 hH.norm0 hH.norm1 hH.distance
  obtain ⟨hH',hz⟩ := physical_relative_gauge cg dg hH
  have hall := (positive_stratum c d H.support0 H.support1 H.norm0 H.norm1 H.distance).mp hpos
  have hB : 0<Real.sqrt (p c 1) := Real.sqrt_pos.mpr (Complex.normSq_pos.mpr (hall.1 1))
  have hG : 0<Real.sqrt (p c 0) := Real.sqrt_pos.mpr (Complex.normSq_pos.mpr (hall.1 0))
  have hS : 0<Real.sqrt (p c 2) := Real.sqrt_pos.mpr (Complex.normSq_pos.mpr (hall.1 2))
  have hh : 0<(1/Real.sqrt 8 : ℝ) := by positivity
  have c3 := congrFun hC ⟨3,by decide⟩
  change cg (bottom ⟨3,by decide⟩)=((1/Real.sqrt 8 : ℝ) : ℂ) at c3
  have hsq : (1/Real.sqrt 8 : ℝ)^2=1/8 := by
    have hf := fixed_alpha cg (tau • dg) hH'.support0 hH'.support1 hH'.norm0 hH'.norm1 hH'.distance
    change Complex.normSq (cg (bottom ⟨3,by decide⟩))=1/8 at hf
    rw [c3,Complex.normSq_ofReal] at hf
    simpa only [pow_two] using hf
  obtain ⟨xi,eta,zeta,hxi,heta,hzeta,hD⟩ := Orbit45TopGauge.top_canonical cg (tau • dg) hH'
    (Real.sqrt (p c 1)) (Real.sqrt (p c 0)) (Real.sqrt (p c 2)) (1/Real.sqrt 8) U V W
    hB hG hS hh hsq hC hz
  exact ⟨theta,tau,U,V,W,xi,eta,zeta,htau,hH',hp,hU,hV,hW,hxi,heta,hzeta,hC,hD⟩
end
end MainTheory.Orbit45PhysicalPhaseNormalForm
