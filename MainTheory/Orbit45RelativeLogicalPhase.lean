import MainTheory.Orbit45PhysicalProbabilityDomain
import MainTheory.Orbit8PhaseNormalization

/-! The positive half-angle kernel parameter can be made exactly 1/8 by
a unit relative logical phase, with every actual physical KL equation kept. -/
set_option autoImplicit false
namespace MainTheory.Orbit45RelativeLogicalPhase
open MainTheory.Orbit45PrintedFibers MainTheory.Orbit45PhysicalPrintedRows
open MainTheory.Orbit45PhysicalProbabilityDomain SixQubit.Orbit45Support
noncomputable section
def phase (c d : SS.State 6 ℂ) : ℂ := (1/8 : ℂ)/z c d 3
theorem fixed_norm (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : Complex.normSq (z c d 3)=1/64 := by
  have hm := product_magnitude c d hc hd hnc hnd hkl 3
  rw [fixed_alpha c d hc hd hnc hnd hkl] at hm
  rw [Complex.normSq_eq_norm_sq,hm]
  norm_num
theorem phase_unit (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : star (phase c d)*phase c d=1 := by
  rw [SixQubit.star_mul_self,phase,Complex.normSq_div,
    fixed_norm c d hc hd hnc hnd hkl]
  norm_num [Complex.normSq_apply]
theorem relative_gauge (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    z c (phase c d • d) 3=1/8 ∧
    (∀ x, x ∉ S1 → (phase c d • d) x=0) ∧
    SS.innerC (phase c d • d) (phase c d • d)=1 ∧
    SS.HasDistance ![c,phase c d • d] 3 := by
  have hu := phase_unit c d hc hd hnc hnd hkl
  have hz : z c d 3 ≠ 0 := by
    intro he
    have h := fixed_norm c d hc hd hnc hnd hkl
    rw [he,Complex.normSq_zero] at h
    norm_num at h
  refine ⟨?_,?_,?_,?_⟩
  · change star (c (bottom 3))*(phase c d*d (top 3))=1/8
    calc
      _ = phase c d*z c d 3 := by unfold z; ring
      _ = _ := div_mul_cancel₀ _ hz
  · intro x hx
    simp [hd x hx]
  · rw [MainTheory.CodeSpec.innerC_smul_left,MainTheory.CodeSpec.innerC_smul_right, hnd]
    simpa only [mul_one] using hu
  · have h := MainTheory.Orbit8PhaseNormalization.rephase_distance ![c,d]
      (![1,phase c d] : Fin 2 → ℂ) (by intro i; fin_cases i; simp; exact hu) hkl
    have he : (fun i : Fin 2 => (![1,phase c d] : Fin 2 → ℂ) i • (![c,d] i))=
        ![c,phase c d • d] := by ext i x; fin_cases i <;> simp
    rwa [he] at h
end
end MainTheory.Orbit45RelativeLogicalPhase
