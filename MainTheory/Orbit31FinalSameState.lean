import MainTheory.Orbit31FinalCross

/-! The final support's same-state equation comes from actual weight-two
Paulis. Together with the cross equations it gives the SI positive identity. -/
set_option autoImplicit false
set_option maxHeartbeats 32000000
namespace MainTheory.Orbit31FinalSameState
noncomputable section
open MainTheory.Orbit31PhaseRatios
open MainTheory.Orbit31CanonicalPhase
open MainTheory.Orbit31PermanentAlgebra
open MainTheory.Orbit31FinalCross
open MainTheory.Generated.Orbit31DirectTriangles.Type02
open SixQubit.Orbit31

def SameStateRow (c d : Fin 16 → ℂ) : Prop :=
  c 4*star (c 7)+c 8*star (c 11)+c 12*star (c 15)+star (c 0)*c 3 =
    star (d 4)*d 7+star (d 8)*d 11+star (d 12)*d 15+d 0*star (d 3)

theorem physical_row (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : SameStateRow (C c) (D d) := by
  have he := fam3_0_3 c d
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef14 w0 (by decide +kernel))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef14 w5 (by decide +kernel))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef14 w4 (by decide +kernel))
    (SixQubit.diagOn_eq_of_hasDistance S0 S1 c d hc hd hkl ef14 w8 (by decide +kernel))
  unfold SameStateRow
  norm_num [C_native,D_native,Fin.succ]
  exact he

theorem same_state {c d : Fin 16 → ℂ} (hp : EqualProbabilities c d)
    (hs : CrossSystem c d) (hm : AmplitudeSupport mask c) (hr : SameStateRow c d) :
    star (c 0)*c 3+star (c 7)*c 4=0 := by
  have hz11 := inactive_zero hm (⟨11,by decide⟩ : Fin 16) (by decide +kernel)
  have hz12 := inactive_zero hm (⟨12,by decide⟩ : Fin 16) (by decide +kernel)
  have hd11 := (complementary_zero_iff hp (⟨11,by decide⟩ : Fin 16)).mpr hz11
  have hd12 := (complementary_zero_iff hp (⟨12,by decide⟩ : Fin 16)).mpr hz12
  simp at hz11 hz12 hd11 hd12
  have h0 := phase_pattern hp hs hm (⟨0,by decide⟩ : Fin 16) (by decide +kernel)
  have h3 := phase_pattern hp hs hm (⟨3,by decide⟩ : Fin 16) (by decide +kernel)
  have h4 := phase_pattern hp hs hm (⟨4,by decide⟩ : Fin 16) (by decide +kernel)
  have h7 := phase_pattern hp hs hm (⟨7,by decide⟩ : Fin 16) (by decide +kernel)
  norm_num [colors,MainTheory.SignedPhaseSupport.sign,Fin.succ] at h0 h3 h4 h7
  simp at h0 h3 h4 h7
  have hunit : sigma c d anchor*star (sigma c d anchor)=1 := by
    have hu := unit_normSq hp ((hm anchor).mp (by decide +kernel))
    have he : ((Complex.normSq (sigma c d anchor) : ℝ) : ℂ)=1 := by exact_mod_cast hu
    rw [Complex.normSq_eq_conj_mul_self] at he
    change star (sigma c d anchor)*sigma c d anchor=1 at he
    simpa only [mul_comm] using he
  have hd7 : d 7=star (sigma c d 7*c 7) := by
    have he := congrArg star (reconstruct hp (7 : Fin 16))
    simpa only [star_star] using he
  have hd0 : d 0=star (sigma c d 0*c 0) := by
    have he := congrArg star (reconstruct hp (0 : Fin 16))
    simpa only [star_star] using he
  have htop : star (d 4)*d 7+d 0*star (d 3)=-(c 4*star (c 7)+star (c 0)*c 3) := by
    rw [reconstruct hp (4 : Fin 16),reconstruct hp (3 : Fin 16),hd7,hd0]
    rw [h0,h3,h4,h7]
    simp only [star_mul,star_neg]
    calc
      _ = -(sigma c d anchor*star (sigma c d anchor))*(c 4*star (c 7)+star (c 0)*c 3) := by ring
      _ = _ := by rw [hunit]; ring
  unfold SameStateRow at hr
  simp [hz11,hz12,hd11,hd12] at hr
  change c 4*star (c 7)+star (c 0)*c 3 = star (d 4)*d 7+d 0*star (d 3) at hr
  rw [htop] at hr
  linear_combination (1/2)*hr

theorem physical_same_state (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (hm : AmplitudeSupport mask (C c)) :
    star (C c 0)*C c 3+star (C c 7)*C c 4=0 :=
  same_state (physical_equal_probabilities c d hc hd hnc hnd hkl)
    (MainTheory.Orbit31PhysicalSupportFilters.physical_cross_system c d hc hd hkl)
    hm (physical_row c d hc hd hkl)

theorem final_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ S0 → c x=0) (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (hm : AmplitudeSupport mask (C c)) : False := by
  have hp := physical_equal_probabilities c d hc hd hnc hnd hkl
  have hs := MainTheory.Orbit31PhysicalSupportFilters.physical_cross_system c d hc hd hkl
  obtain ⟨K,_,hK⟩ := MainTheory.Orbit31FinalCross.Type02.commonK hp hs hm
  apply positive_contradiction (C c 0) (C c 3) (C c 4) (C c 7) K
    ((hm _).mp (by decide +kernel)) ((hm _).mp (by decide +kernel))
    (hK 0) (hK 3)
  exact physical_same_state c d hc hd hnc hnd hkl hm

end
end MainTheory.Orbit31FinalSameState
