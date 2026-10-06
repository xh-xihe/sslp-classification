import MainTheory.Orbit12AnchorLines
set_option autoImplicit false
namespace MainTheory.Orbit12AnchorScalars
open scoped Matrix BigOperators
open SixQubit.Orbit12 MainTheory.Orbit12Frames MainTheory.Orbit12MomentDisplays
open MainTheory.Orbit12AnchorLines
noncomputable section

def unitBottom (c : SS.State 6 ℂ) : Fin 2 → ℂ := (2 : ℂ) • u c
def unitTop (d : SS.State 6 ℂ) : Fin 2 → ℂ := (2 : ℂ) • ut d
def nsq (x : Fin 2 → ℂ) : ℝ := Complex.normSq (x 0)+Complex.normSq (x 1)

theorem scale_two_unit (x : Fin 2 → ℂ) (h : nsq x=1/4) : nsq ((2 : ℂ) • x)=1 := by
  simp only [nsq,Pi.smul_apply,smul_eq_mul,map_mul] at h ⊢
  norm_num
  nlinarith

theorem actual_anchor_scalars (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∃ alpha0 alpha4 beta0 beta4 : ℂ,
      nsq (unitBottom c)=1 ∧ nsq (unitTop d)=1 ∧
      u c=alpha0 • unitBottom c ∧ v c=alpha4 • unitBottom c ∧
      ut d=beta0 • unitTop d ∧ vt d=beta4 • unitTop d := by
  obtain ⟨⟨t,ht⟩,⟨s,hs⟩⟩ := actual_anchor_lines c d hc hd hnc hnd hkl
  have hm := physical_moments c d hc hd hnc hnd hkl
  have hu := bottom_zero_anchor _ _ hm
  have hU := top_zero_anchor _ _ hm
  change nsq (u c)=1/4 at hu
  change nsq (ut d)=1/4 at hU
  refine ⟨1/2,t/2,1/2,s/2,scale_two_unit _ hu,scale_two_unit _ hU,?_,?_,?_,?_⟩
  · funext i
    simp only [unitBottom,Pi.smul_apply,smul_eq_mul]
    ring
  · rw [ht]
    funext i
    simp only [unitBottom,Pi.smul_apply,smul_eq_mul]
    ring
  · funext i
    simp only [unitTop,Pi.smul_apply,smul_eq_mul]
    ring
  · rw [hs]
    funext i
    simp only [unitTop,Pi.smul_apply,smul_eq_mul]
    ring

end
end MainTheory.Orbit12AnchorScalars
