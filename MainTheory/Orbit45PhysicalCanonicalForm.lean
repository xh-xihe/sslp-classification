import MainTheory.Orbit45PhysicalPhaseNormalForm

/-! Every actual positive-stratum solution has the final printed canonical
amplitudes and vector triangle, obtained from its physical KL equations. -/
set_option autoImplicit false
namespace MainTheory.Orbit45PhysicalCanonicalForm
open MainTheory.Orbit45PrintedFibers MainTheory.Orbit45PhysicalPrintedRows
open MainTheory.Orbit45PhysicalGauge MainTheory.Orbit45AffineGauge
open MainTheory.Orbit45PhysicalProbabilityDomain MainTheory.Orbit45CrossFactors
noncomputable section

theorem physical_forced_phases (c d : SS.State 6 ℂ) (H : FullKL c d)
    (B G S h : ℝ) (U V W xi eta zeta : ℂ)
    (hB : 0<B) (hG : 0<G) (hS : 0<S) (hh : 0<h)
    (hU : Complex.normSq U=1) (hV : Complex.normSq V=1) (hW : Complex.normSq W=1)
    (hxi : Complex.normSq xi=1) (heta : Complex.normSq eta=1)
    (hC : (fun i => c (bottom i))=C B G S h U V W)
    (hD : (fun i => d (top i))=D B G S h U V W xi eta zeta) :
    U=-1 ∧ V=star xi ∧ W=star eta ∧ zeta=1 := by
  have b0 : (B : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  have g0 : (G : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hG
  have s0 : (S : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hS
  have h0 : (h : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hh
  have f0 := Row0.physical_factors B G S h U V W xi eta zeta hU hV hW
    (mul_ne_zero b0 h0) c d H.support0 H.support1 H.distance hC hD
  have f1 := Row1.physical_factors B G S h U V W xi eta zeta hU hV hW
    (mul_ne_zero (mul_ne_zero (by norm_num) s0) h0) c d H.support0 H.support1 H.distance hC hD
  have f2 := Row2.physical_factors B G S h U V W xi eta zeta hU hV hW
    (mul_ne_zero g0 h0) c d H.support0 H.support1 H.distance hC hD
  have f3 := Row3.physical_factors B G S h U V W xi eta zeta hU hV hW
    (mul_ne_zero b0 h0) c d H.support0 H.support1 H.distance hC hD
  exact forced_phases U V W xi eta zeta hxi heta f0 f1 f2 f3

theorem physical_triangle (c d : SS.State 6 ℂ) (H : FullKL c d)
    (B G S h : ℝ) (U V W xi eta zeta : ℂ)
    (hC : (fun i => c (bottom i))=C B G S h U V W)
    (hD : (fun i => d (top i))=D B G S h U V W xi eta zeta) :
    ((B^2 : ℝ) : ℂ)*xi+((G^2 : ℝ) : ℂ)*eta+((S^2 : ℝ) : ℂ)*zeta=0 := by
  have hk := congrFun (physical_cross_kernel c d H.support0 H.support1 H.distance) ⟨2,by decide⟩
  change z c d ⟨2,by decide⟩= -z c d 1-z c d 0 at hk
  simp only [z] at hk
  have c0 := congrFun hC ⟨0,by decide⟩
  have c1 := congrFun hC ⟨1,by decide⟩
  have c2 := congrFun hC ⟨2,by decide⟩
  have d0 := congrFun hD ⟨0,by decide⟩
  have d1 := congrFun hD ⟨1,by decide⟩
  have d2 := congrFun hD ⟨2,by decide⟩
  norm_num [C,D] at c0 c1 c2 d0 d1 d2
  rw [c0,c1,c2,d0,d1,d2] at hk
  simp only [Complex.star_def,Complex.conj_ofReal] at hk
  push_cast
  linear_combination hk

theorem physical_canonical_form (c d : SS.State 6 ℂ) (H : FullKL c d)
    (hpos : 0<p c 1*p c 0*p c 2) :
    ∃ (theta : Fin 7 → ℝ) (tau xi eta : ℂ),
      let c' := phaseAction theta c
      let d' := tau • phaseAction theta d
      star tau*tau=1 ∧ FullKL c' d' ∧ p c'=p c ∧
      Complex.normSq xi=1 ∧ Complex.normSq eta=1 ∧
      (p c 1 : ℂ)*xi+(p c 0 : ℂ)*eta+(p c 2 : ℂ)=0 ∧
      (fun i => c' (bottom i))=C
        (Real.sqrt (p c 1)) (Real.sqrt (p c 0)) (Real.sqrt (p c 2)) (1/Real.sqrt 8) (-1) (star xi) (star eta) ∧
      (fun i => d' (top i))=D
        (Real.sqrt (p c 1)) (Real.sqrt (p c 0)) (Real.sqrt (p c 2)) (1/Real.sqrt 8) (-1) (star xi) (star eta) xi eta 1 := by
  obtain ⟨theta,tau,U,V,W,xi,eta,zeta,htau,hH,hp,hU,hV,hW,hxi,heta,_,hC,hD⟩ :=
    Orbit45PhysicalPhaseNormalForm.physical_phase_normal_form c d H hpos
  have hall := (positive_stratum c d H.support0 H.support1 H.norm0 H.norm1 H.distance).mp hpos
  have hB : 0<Real.sqrt (p c 1) := Real.sqrt_pos.mpr (Complex.normSq_pos.mpr (hall.1 1))
  have hG : 0<Real.sqrt (p c 0) := Real.sqrt_pos.mpr (Complex.normSq_pos.mpr (hall.1 0))
  have hS : 0<Real.sqrt (p c 2) := Real.sqrt_pos.mpr (Complex.normSq_pos.mpr (hall.1 2))
  have hh : 0<(1/Real.sqrt 8 : ℝ) := by positivity
  obtain ⟨hu,hv,hw,hz⟩ := physical_forced_phases _ _ hH
    (Real.sqrt (p c 1)) (Real.sqrt (p c 0)) (Real.sqrt (p c 2)) (1/Real.sqrt 8)
    U V W xi eta zeta hB hG hS hh hU hV hW hxi heta hC hD
  have htriangle := physical_triangle _ _ hH
    (Real.sqrt (p c 1)) (Real.sqrt (p c 0)) (Real.sqrt (p c 2)) (1/Real.sqrt 8)
    U V W xi eta zeta hC hD
  rw [Real.sq_sqrt (show 0≤p c 1 from Complex.normSq_nonneg _),
    Real.sq_sqrt (show 0≤p c 0 from Complex.normSq_nonneg _),
    Real.sq_sqrt (show 0≤p c 2 from Complex.normSq_nonneg _),hz,mul_one] at htriangle
  rw [hu,hv,hw] at hC
  rw [hu,hv,hw,hz] at hD
  exact ⟨theta,tau,xi,eta,htau,hH,hp,hxi,heta,htriangle,hC,hD⟩
end
end MainTheory.Orbit45PhysicalCanonicalForm
