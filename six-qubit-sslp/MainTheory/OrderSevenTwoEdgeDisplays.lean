import MainTheory.OrderSevenSupportDisplays
import MainTheory.TwoEdgeWalshDisplays

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace MainTheory.OrderSevenTwoEdgeDisplays
open MainTheory.OrderSevenSupportDisplays MainTheory.FlipCharacter
open MainTheory.OrderEightSupportDisplays (bits)


namespace Orbit57
open SixQubit.Orbit57 (S0 S1)
noncomputable def U (c d : SS.State 6 ℂ) := star (c (bottom57 0))*d (top57 6)
noncomputable def V (c d : SS.State 6 ℂ) := star (c (bottom57 6))*d (top57 0)

theorem incidence : incidenceSet S0 S1 (SS.stdBasis 0)={bits 32,bits 63} := by decide +kernel
theorem labels : top57 6=bits 32 ∧ top57 0=bits 63 ∧
    SS.bxor (bits 32) (SS.stdBasis 0)=bottom57 0 ∧
    SS.bxor (bits 63) (SS.stdBasis 0)=bottom57 6 := by decide +kernel

theorem equations (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : U c d+V c d=0 ∧ U c d-V c d=0 := by
  have h := MainTheory.TwoEdgeWalshDisplays.equations S0 S1 c d hc hd hkl 0 1 (bits 32) (bits 63)
    incidence (by decide +kernel)
  obtain ⟨hl0,hl1,hf0,hf1⟩ := labels
  rw [hf0,hf1] at h
  simpa only [← hl0,← hl1] using h

theorem magnitudes (c d : SS.State 6 ℂ)
    (hc0 : Complex.normSq (c (bottom57 0))=5/14)
    (hc1 : Complex.normSq (c (bottom57 6))=1/7)
    (hd0 : Complex.normSq (d (top57 0))=5/14)
    (hd1 : Complex.normSq (d (top57 6))=1/7) :
    ‖U c d‖=Real.sqrt ((5/14 : ℝ)*(1/7)) ∧
    ‖V c d‖=Real.sqrt ((5/14 : ℝ)*(1/7)) ∧ 0<Real.sqrt ((5/14 : ℝ)*(1/7)) := by
  constructor
  · rw [U,Complex.norm_def,Complex.normSq_mul,Complex.star_def,Complex.normSq_conj,hc0,hd1]
  constructor
  · rw [V,Complex.norm_def,Complex.normSq_mul,Complex.star_def,Complex.normSq_conj,hc1,hd0,mul_comm]
  · positivity

end Orbit57


namespace Orbit59
open SixQubit.Orbit59 (S0 S1)
noncomputable def U (c d : SS.State 6 ℂ) := star (c (bottom59 0))*d (top59 6)
noncomputable def V (c d : SS.State 6 ℂ) := star (c (bottom59 6))*d (top59 0)

theorem incidence : incidenceSet S0 S1 (SS.stdBasis 0)={bits 32,bits 63} := by decide +kernel
theorem labels : top59 6=bits 32 ∧ top59 0=bits 63 ∧
    SS.bxor (bits 32) (SS.stdBasis 0)=bottom59 0 ∧
    SS.bxor (bits 63) (SS.stdBasis 0)=bottom59 6 := by decide +kernel

theorem equations (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : U c d+V c d=0 ∧ U c d-V c d=0 := by
  have h := MainTheory.TwoEdgeWalshDisplays.equations S0 S1 c d hc hd hkl 0 1 (bits 32) (bits 63)
    incidence (by decide +kernel)
  obtain ⟨hl0,hl1,hf0,hf1⟩ := labels
  rw [hf0,hf1] at h
  simpa only [← hl0,← hl1] using h

theorem magnitudes (c d : SS.State 6 ℂ)
    (hc0 : Complex.normSq (c (bottom59 0))=2/7)
    (hc1 : Complex.normSq (c (bottom59 6))=3/14)
    (hd0 : Complex.normSq (d (top59 0))=2/7)
    (hd1 : Complex.normSq (d (top59 6))=3/14) :
    ‖U c d‖=Real.sqrt ((2/7 : ℝ)*(3/14)) ∧
    ‖V c d‖=Real.sqrt ((2/7 : ℝ)*(3/14)) ∧ 0<Real.sqrt ((2/7 : ℝ)*(3/14)) := by
  constructor
  · rw [U,Complex.norm_def,Complex.normSq_mul,Complex.star_def,Complex.normSq_conj,hc0,hd1]
  constructor
  · rw [V,Complex.norm_def,Complex.normSq_mul,Complex.star_def,Complex.normSq_conj,hc1,hd0,mul_comm]
  · positivity

end Orbit59


namespace Orbit60
open SixQubit.Orbit60 (S0 S1)
noncomputable def U (c d : SS.State 6 ℂ) := star (c (bottom60 0))*d (top60 8)
noncomputable def V (c d : SS.State 6 ℂ) := star (c (bottom60 8))*d (top60 0)

theorem incidence : incidenceSet S0 S1 (SS.stdBasis 0)={bits 32,bits 63} := by decide +kernel
theorem labels : top60 8=bits 32 ∧ top60 0=bits 63 ∧
    SS.bxor (bits 32) (SS.stdBasis 0)=bottom60 0 ∧
    SS.bxor (bits 63) (SS.stdBasis 0)=bottom60 8 := by decide +kernel

theorem equations (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : U c d+V c d=0 ∧ U c d-V c d=0 := by
  have h := MainTheory.TwoEdgeWalshDisplays.equations S0 S1 c d hc hd hkl 0 1 (bits 32) (bits 63)
    incidence (by decide +kernel)
  obtain ⟨hl0,hl1,hf0,hf1⟩ := labels
  rw [hf0,hf1] at h
  simpa only [← hl0,← hl1] using h

theorem magnitudes (c d : SS.State 6 ℂ)
    (hc0 : Complex.normSq (c (bottom60 0))=3/14)
    (hc1 : Complex.normSq (c (bottom60 8))=2/7)
    (hd0 : Complex.normSq (d (top60 0))=3/14)
    (hd1 : Complex.normSq (d (top60 8))=2/7) :
    ‖U c d‖=Real.sqrt ((3/14 : ℝ)*(2/7)) ∧
    ‖V c d‖=Real.sqrt ((3/14 : ℝ)*(2/7)) ∧ 0<Real.sqrt ((3/14 : ℝ)*(2/7)) := by
  constructor
  · rw [U,Complex.norm_def,Complex.normSq_mul,Complex.star_def,Complex.normSq_conj,hc0,hd1]
  constructor
  · rw [V,Complex.norm_def,Complex.normSq_mul,Complex.star_def,Complex.normSq_conj,hc1,hd0,mul_comm]
  · positivity

end Orbit60


end MainTheory.OrderSevenTwoEdgeDisplays
