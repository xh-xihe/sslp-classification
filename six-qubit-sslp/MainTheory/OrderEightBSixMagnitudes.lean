import MainTheory.OrderEightBFlipDisplays
import MainTheory.OrderEightMomentFaces

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.OrderEightBSixMagnitudes

open MainTheory.OrderEightBFlipDisplays MainTheory.OrderEightSupportDisplays
open MainTheory.OrderEightMomentFaces MainTheory.MomentPolytope

theorem labels : bottomB 3=bits 38 ∧ topB 3=bits 25 ∧
    bottomB 4=bits 49 ∧ topB 4=bits 14 ∧ bottomB 7=bits 31 ∧ topB 7=bits 32 := by
  decide +kernel

theorem magnitudes (c d : SS.State 6 ℂ) (p : Sum (Fin 8) (Fin 8) → ℝ)
    (H : Feasible bottomB topB p)
    (hc : ∀ i,Complex.normSq (c (bottomB i))=p (Sum.inl i))
    (hd : ∀ i,Complex.normSq (d (topB i))=p (Sum.inr i)) :
    Complex.normSq (alpha0 c)=3/16 ∧ Complex.normSq (alpha1 d)=3/16 ∧
    Complex.normSq (beta0 c)=1/8 ∧ Complex.normSq (beta1 d)=1/8 ∧
    Complex.normSq (gamma0 c)=p (Sum.inl 0)+1/16 ∧
    Complex.normSq (gamma1 d)=p (Sum.inl 0)+1/16 := by
  obtain ⟨h0,h1⟩ := probabilities_B p H
  have hl := labels
  have hc3 := hc 3
  have hd3 := hd 3
  have hc4 := hc 4
  have hd4 := hd 4
  have hc7 := hc 7
  have hd7 := hd 7
  rw [hl.1,congrFun h0 3] at hc3
  rw [hl.2.1,congrFun h1 3] at hd3
  rw [hl.2.2.1,congrFun h0 4] at hc4
  rw [hl.2.2.2.1,congrFun h1 4] at hd4
  rw [hl.2.2.2.2.1,congrFun h0 7] at hc7
  rw [hl.2.2.2.2.2,congrFun h1 7] at hd7
  exact ⟨hc3,hd3,hc4,hd4,hc7,hd7⟩

theorem all_nonzero (c d : SS.State 6 ℂ) (p : Sum (Fin 8) (Fin 8) → ℝ)
    (H : Feasible bottomB topB p)
    (hc : ∀ i,Complex.normSq (c (bottomB i))=p (Sum.inl i))
    (hd : ∀ i,Complex.normSq (d (topB i))=p (Sum.inr i)) :
    alpha0 c ≠ 0 ∧ alpha1 d ≠ 0 ∧ beta0 c ≠ 0 ∧ beta1 d ≠ 0 ∧
    gamma0 c ≠ 0 ∧ gamma1 d ≠ 0 := by
  obtain ⟨ha,ha',hb,hb',hg,hg'⟩ := magnitudes c d p H hc hd
  have ht := H.nonneg (Sum.inl 0)
  have nonzero (z : ℂ) (h : 0 < Complex.normSq z) : z ≠ 0 := by
    intro hz
    simp [hz] at h
  exact ⟨nonzero _ (by rw [ha]; norm_num),nonzero _ (by rw [ha']; norm_num),
    nonzero _ (by rw [hb]; norm_num),nonzero _ (by rw [hb']; norm_num),
    nonzero _ (by rw [hg]; linarith),nonzero _ (by rw [hg']; linarith)⟩

end MainTheory.OrderEightBSixMagnitudes
