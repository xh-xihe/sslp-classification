import MainTheory.Orbit45PrintedWalsh
import MainTheory.Orbit45PrintedAttainment

/-! The literal half-angle kernel forces the fixed mass and triangle domain. -/

namespace MainTheory.Orbit45PrintedConsequences

noncomputable section

open MainTheory.Orbit45PrintedWalsh

theorem fixed_mass (alpha : ℝ) (z : Fin 10 → ℂ)
    (hz : W.mulVec z = 0)
    (h3 : ‖z 3‖ = alpha) (h4 : ‖z 4‖ = 1/4-alpha) :
    alpha = 1/8 ∧ ‖z 3‖ = 1/8 := by
  have he : z 4 = -z 3 := congrFun ((kernel_iff z).1 hz) 4
  rw [he,norm_neg] at h4
  constructor <;> linarith

theorem triangle_bounds (b c s : ℝ) (B C : ℂ)
    (hb : ‖B‖ = b) (hc : ‖C‖ = c) (hs : ‖B+C‖ = s)
    (htotal : b+c+s = 1/4) :
    0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ s ∧ b ≤ 1/8 ∧ c ≤ 1/8 ∧ s ≤ 1/8 := by
  have hbc := norm_add_le B C
  have hbs := norm_add_le (B+C) (-C)
  have hcs := norm_add_le (B+C) (-B)
  have heB : B+C+(-C) = B := by ring
  have heC : B+C+(-B) = C := by ring
  rw [heB,norm_neg,hb,hc,hs] at hbs
  rw [heC,norm_neg,hb,hc,hs] at hcs
  rw [hb,hc,hs] at hbc
  exact ⟨hb ▸ norm_nonneg B,hc ▸ norm_nonneg C,hs ▸ norm_nonneg (B+C),
    by linarith,by linarith,by linarith⟩

def unitPhase (z : ℂ) : ℂ := if z=0 then 1 else z/‖z‖

theorem unitPhase_normSq (z : ℂ) : Complex.normSq (unitPhase z) = 1 := by
  by_cases hz : z=0
  · simp [unitPhase,hz]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    rw [unitPhase,if_neg hz,Complex.normSq_div,Complex.normSq_ofReal,
      Complex.normSq_eq_norm_sq]
    field_simp

theorem unitPhase_value (z : ℂ) : (‖z‖ : ℂ)*unitPhase z = z := by
  by_cases hz : z=0
  · simp [unitPhase,hz]
  · have hn : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
    rw [unitPhase,if_neg hz]
    exact mul_div_cancel₀ z hn

theorem triangle_phases (b c s : ℝ) (B C : ℂ)
    (hb : ‖B‖ = b) (hc : ‖C‖ = c) (hs : ‖B+C‖ = s) :
    ∃ xi eta zeta : ℂ,
      Complex.normSq xi = 1 ∧ Complex.normSq eta = 1 ∧ Complex.normSq zeta = 1 ∧
      (b : ℂ)*xi = B ∧ (c : ℂ)*eta = C ∧
      (b : ℂ)*xi+(c : ℂ)*eta+(s : ℂ)*zeta = 0 := by
  refine ⟨unitPhase B,unitPhase C,unitPhase (-(B+C)),unitPhase_normSq _,
    unitPhase_normSq _,unitPhase_normSq _,?_,?_,?_⟩
  · rw [← hb]; exact unitPhase_value B
  · rw [← hc]; exact unitPhase_value C
  · have hn : ‖-(B+C)‖=s := by rw [norm_neg,hs]
    rw [← hb,unitPhase_value,← hc,unitPhase_value,← hn,unitPhase_value]
    ring

end

end MainTheory.Orbit45PrintedConsequences
