import MainTheory.Orbit45PhysicalGauge
import MainTheory.Orbit45CrossFactors

/-! Every supported physical solution admits the literal printed bottom
amplitudes after physical diagonal phases and a common logical phase. -/
set_option autoImplicit false
namespace MainTheory.Orbit45BottomGauge
open MainTheory.Orbit45PrintedFibers MainTheory.Orbit45PhysicalPrintedRows
open MainTheory.Orbit45PhysicalGauge MainTheory.Orbit45AffineGauge
open MainTheory.Orbit45PhysicalProbabilityDomain
noncomputable section

theorem equal_norm (c : SS.State 6 ℂ) (i j : Fin 10) (he : p c i=p c j) :
    ‖c (bottom i)‖=‖c (bottom j)‖ := by
  rw [Complex.norm_def,Complex.norm_def]
  exact congrArg Real.sqrt he

theorem physical_norms (c d : SS.State 6 ℂ) (H : FullKL c d) :
    ‖c (bottom 4)‖=‖c (bottom 3)‖ ∧
    ‖c (bottom 5)‖=‖c (bottom 3)‖ ∧
    ‖c (bottom 6)‖=‖c (bottom 3)‖ ∧
    ‖c (bottom 7)‖=‖c (bottom 2)‖ ∧
    ‖c (bottom 8)‖=‖c (bottom 1)‖ ∧
    ‖c (bottom 9)‖=‖c (bottom 0)‖ := by
  have hp := (physical_probabilities c d H.support0 H.support1 H.norm0 H.norm1 H.distance).1
  have he : ∀ i j : Fin 10,
      Orbit45PrintedMoments.pattern (1/8) (p c 1) (p c 0) i=
        Orbit45PrintedMoments.pattern (1/8) (p c 1) (p c 0) j →
      ‖c (bottom i)‖=‖c (bottom j)‖ := by
    intro i j hij
    apply equal_norm c i j
    rw [hp,hij]
  refine ⟨he ⟨4,by decide⟩ ⟨3,by decide⟩ ?_,he ⟨5,by decide⟩ ⟨3,by decide⟩ ?_,
    he ⟨6,by decide⟩ ⟨3,by decide⟩ ?_,he ⟨7,by decide⟩ ⟨2,by decide⟩ ?_,
    he ⟨8,by decide⟩ ⟨1,by decide⟩ ?_,he ⟨9,by decide⟩ ⟨0,by decide⟩ ?_⟩ <;>
    norm_num [Orbit45PrintedMoments.pattern]

theorem bottom_canonical (c d : SS.State 6 ℂ) (H : FullKL c d)
    (ha : ∀ i : Fin 7, c (bottom (anchors i))=(‖c (bottom (anchors i))‖ : ℂ)) :
    ∃ U V W : ℂ, Complex.normSq U=1 ∧ Complex.normSq V=1 ∧ Complex.normSq W=1 ∧
      (fun i => c (bottom i))=Orbit45CrossFactors.C
        ‖c (bottom 1)‖ ‖c (bottom 0)‖ ‖c (bottom 2)‖ ‖c (bottom 3)‖ U V W := by
  let U := Orbit45PrintedConsequences.unitPhase (c (bottom 6))
  let V := Orbit45PrintedConsequences.unitPhase (c (bottom 8))
  let W := Orbit45PrintedConsequences.unitPhase (c (bottom 9))
  refine ⟨U,V,W,Orbit45PrintedConsequences.unitPhase_normSq _,
    Orbit45PrintedConsequences.unitPhase_normSq _,Orbit45PrintedConsequences.unitPhase_normSq _,?_⟩
  obtain ⟨h4,h5,h6,h7,h8,h9⟩ := physical_norms c d H
  have a0 := ha ⟨0,by decide⟩
  have a1 := ha ⟨1,by decide⟩
  have a2 := ha ⟨2,by decide⟩
  have a3 := ha ⟨3,by decide⟩
  have a4 := ha ⟨4,by decide⟩
  have a5 := ha ⟨5,by decide⟩
  have a7 := ha ⟨6,by decide⟩
  norm_num [anchors] at a0 a1 a2 a3 a4 a5 a7
  have a6 := Orbit45PrintedConsequences.unitPhase_value (c (bottom 6))
  have a8 := Orbit45PrintedConsequences.unitPhase_value (c (bottom 8))
  have a9 := Orbit45PrintedConsequences.unitPhase_value (c (bottom 9))
  rw [h6] at a6
  rw [h8] at a8
  rw [h9] at a9
  funext i
  fin_cases i <;> norm_num only [Orbit45CrossFactors.C,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Fin.mk_one,Fin.mk_zero] <;>
    first | exact a0 | exact a1 | exact a2 | exact a3 | simpa only [h4] using a4 |
      simpa only [h5] using a5 | exact a6.symm | simpa only [h7] using a7 |
      exact a8.symm | exact a9.symm

theorem half_amplitude (c d : SS.State 6 ℂ) (H : FullKL c d) :
    ‖c (bottom 3)‖=1/Real.sqrt 8 := by
  have h := fixed_alpha c d H.support0 H.support1 H.norm0 H.norm1 H.distance
  rw [Complex.norm_def]
  change Real.sqrt (p c 3)=_
  rw [h,Real.sqrt_div (by norm_num),Real.sqrt_one]

theorem physical_bottom_gauge (c d : SS.State 6 ℂ) (H : FullKL c d) :
    ∃ (theta : Fin 7 → ℝ) (U V W : ℂ),
      let c' := phaseAction theta c
      let d' := phaseAction theta d
      FullKL c' d' ∧ p c'=p c ∧ q d'=q d ∧
      Complex.normSq U=1 ∧ Complex.normSq V=1 ∧ Complex.normSq W=1 ∧
      (fun i => c' (bottom i))=Orbit45CrossFactors.C
        (Real.sqrt (p c 1)) (Real.sqrt (p c 0)) (Real.sqrt (p c 2)) (1/Real.sqrt 8) U V W := by
  obtain ⟨theta,hH,hp,hq,ha⟩ := physical_anchor_gauge c d H
  have ha' : ∀ i : Fin 7,
      phaseAction theta c (bottom (anchors i))=
        (‖phaseAction theta c (bottom (anchors i))‖ : ℂ) := by
    intro i
    have hn : ‖phaseAction theta c (bottom (anchors i))‖=‖c (bottom (anchors i))‖ := by
      rw [Complex.norm_def,phaseAction_normSq,← Complex.norm_def]
    rw [hn]
    exact ha i
  obtain ⟨U,V,W,hU,hV,hW,hC⟩ := bottom_canonical _ _ hH ha'
  refine ⟨theta,U,V,W,hH,hp,hq,hU,hV,hW,?_⟩
  have hB : ‖phaseAction theta c (bottom 1)‖=Real.sqrt (p c 1) := by
    rw [Complex.norm_def,phaseAction_normSq]; rfl
  have hG : ‖phaseAction theta c (bottom 0)‖=Real.sqrt (p c 0) := by
    rw [Complex.norm_def,phaseAction_normSq]; rfl
  have hS : ‖phaseAction theta c (bottom 2)‖=Real.sqrt (p c 2) := by
    rw [Complex.norm_def,phaseAction_normSq]; rfl
  rw [hB,hG,hS,half_amplitude _ _ hH] at hC
  exact hC
end
end MainTheory.Orbit45BottomGauge
