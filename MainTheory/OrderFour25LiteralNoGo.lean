import MainTheory.OrderFour25Magnitudes
import MainTheory.OrderFour25AnchorFlip
import MainTheory.OrderFour25CoherenceAlgebra
import MainTheory.OrderFour25Diagonal

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace MainTheory.OrderFour25LiteralNoGo
open MainTheory.OrderFour25Support MainTheory.OrderFour25Walsh
open MainTheory.OrderFour25CoherenceAlgebra MainTheory.MomentPolytope
open MainTheory.OrderFour25Diagonal
open SixQubit.Orbit25 (S0 S1)

noncomputable def A (c : SS.State 6 ℂ) : ℂ := star (c (anchor false))*c (anchor true)
noncomputable def S (d : SS.State 6 ℂ) : ℂ := star (d (full false))*d (full true)

theorem coherences (c d : SS.State 6 ℂ)
    (ha : ∀ b,Complex.normSq (c (anchor b))=3/16 ∧ Complex.normSq (d (full b))=3/16)
    (ht : ∀ b j,Complex.normSq (c (hat b j))=1/16 ∧ Complex.normSq (d (tail b j))=1/16)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    S d= -A c ∧
    (∀ j,star (d (tail false j))*d (tail true j)= -A c/3 ∧
      star (c (hat false j))*c (hat true j)= -S d/3) := by
  constructor
  · obtain ⟨l,h0,_,_,h3⟩ := kernel_relations c d hc hd hkl 0
    have hr : d (tail false 0) ≠ 0 := by
      intro hz
      have h := (ht false 0).2
      rw [hz] at h
      norm_num at h
    exact opposite_anchors _ _ _ _ _ _ (ha true).1 (ha false).2 hr
      (h3.trans h0.symm) (MainTheory.OrderFour25AnchorFlip.equation c d hc hd hkl 0)
  · intro j
    obtain ⟨l,h0,h1,h2,h3⟩ := kernel_relations c d hc hd hkl j
    have hR : star (c (anchor false))*d (tail false j)+star (c (anchor true))*d (tail true j)=0 := by
      linear_combination h0+h1
    have hB : star (c (hat false j))*d (full false)+star (c (hat true j))*d (full true)=0 := by
      linear_combination h2+h3
    have hBc := congrArg star hB
    simp only [star_add,star_mul',star_star,star_zero] at hBc
    have hB' : star (d (full false))*c (hat false j)+star (d (full true))*c (hat true j)=0 := by
      linear_combination hBc
    exact ⟨tail_coherence _ _ _ _ (ha true).1 (ht false j).2 hR,
      tail_coherence _ _ _ _ (ha true).2 (ht false j).1 hB'⟩

theorem total_coherences (c d : SS.State 6 ℂ)
    (h : ∀ j,star (d (tail false j))*d (tail true j)= -A c/3 ∧
      star (c (hat false j))*c (hat true j)= -S d/3) :
    K0 c=A c-(5/3)*S d ∧ K1 d=S d-(5/3)*A c := by
  constructor
  · simp only [K0,h,A,Fin.sum_univ_succ]
    ring
  · simp only [K1,h,S,Fin.sum_univ_succ]
    ring

theorem no_go (c d : SS.State 6 ℂ) (p : Sum (Fin 12) (Fin 12) → ℝ)
    (H : Feasible bottom top p)
    (hnc : ∀ i,Complex.normSq (c (bottom i))=p (Sum.inl i))
    (hnd : ∀ i,Complex.normSq (d (top i))=p (Sum.inr i))
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  obtain ⟨ha,ht⟩ := MainTheory.OrderFour25Magnitudes.actual c d p H hnc hnd hc hd hkl
  obtain ⟨hop,hco⟩ := coherences c d ha ht hc hd hkl
  have he := equal_of_KL c d hc hd hkl
  obtain ⟨h0,h1⟩ := total_coherences c d hco
  rw [h0,h1] at he
  have hn : A c ≠ 0 := by
    intro hz
    have hsq := congrArg Complex.normSq hz
    simp only [A,Complex.normSq_mul,Complex.star_def,Complex.normSq_conj] at hsq
    rw [(ha false).1,(ha true).1] at hsq
    norm_num at hsq
  exact MainTheory.OrderFour25Pinning.coherence_contradiction (A c) (S d) hn he hop

end MainTheory.OrderFour25LiteralNoGo
