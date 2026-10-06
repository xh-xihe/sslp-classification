import MainTheory.OrderFour25CoordinateMoments
import MainTheory.OrderFour25Walsh
import MainTheory.OrderFour25Pinning

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace MainTheory.OrderFour25Forced
open MainTheory.OrderFour25Support MainTheory.OrderFour25Moments
open MainTheory.OrderFour25CoordinateMoments MainTheory.OrderFour25Walsh
open MainTheory.MomentPolytope
open SixQubit.Orbit25 (S0 S1)

theorem parameters_forced (c d : SS.State 6 ℂ) (p : Sum (Fin 12) (Fin 12) → ℝ)
    (H : Feasible bottom top p)
    (hnc : ∀ i,Complex.normSq (c (bottom i))=p (Sum.inl i))
    (hnd : ∀ i,Complex.normSq (d (top i))=p (Sum.inr i))
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    parameters p=(fun _ => 1/16) ∧ p (Sum.inr 11)=3/16 := by
  let t := parameters p
  let sigma := p (Sum.inr 11)
  let T := total t sigma
  have hp := probabilities p H
  have hb : ∀ i,Complex.normSq (c (bottom i))=bot t sigma i :=
    fun i => (hnc i).trans (congrFun hp.1 i)
  have hu : ∀ i,Complex.normSq (d (top i))=up t sigma i :=
    fun i => (hnd i).trans (congrFun hp.2 i)
  have vals := coordinate_values t sigma
  have ma0 : Complex.normSq (c (anchor false))=3/8-3*T/4+sigma := by
    rw [anchor_index,hb]; exact vals.1
  have ma1 : Complex.normSq (c (anchor true))=3*T/4-sigma := by
    rw [anchor_index,hb]; exact vals.2.1
  have ms0 : Complex.normSq (d (full false))=3/8-sigma := by
    rw [full_index,hu]; exact vals.2.2.1
  have mr0 : ∀ j,Complex.normSq (d (tail false j))=1/8-t j := by
    intro j; rw [tail_index,hu]; exact (vals.2.2.2.2 j).2.2.1
  have mr1 : ∀ j,Complex.normSq (d (tail true j))=t j := by
    intro j; rw [tail_index,hu]; exact (vals.2.2.2.2 j).2.2.2
  have mb0 : ∀ j,Complex.normSq (c (hat false j))=1/8-T/4+t j := by
    intro j; rw [hat_index,hb]; exact (vals.2.2.2.2 j).1
  have mag : ∀ j,(3/8-3*T/4+sigma)*(1/8-t j)=(3*T/4-sigma)*t j ∧
      (3/8-3*T/4+sigma)*(1/8-t j)=(1/8-T/4+t j)*(3/8-sigma) := by
    intro j
    obtain ⟨l,h0,h1,h2,_⟩ := kernel_relations c d hc hd hkl j
    have he1 := congrArg Complex.normSq (h1.trans (congrArg Neg.neg h0.symm))
    have he2 := congrArg Complex.normSq (h2.trans (congrArg Neg.neg h0.symm))
    simp only [Complex.normSq_neg,Complex.normSq_mul,Complex.star_def,Complex.normSq_conj,
      ma0,ma1,ms0,mr0,mr1,mb0] at he1 he2
    exact ⟨he1.symm,he2.symm⟩
  have ht : ∀ j,3/8-3*T/4+sigma=3*t j := by
    intro j
    exact MainTheory.OrderFour25Pinning.tail_parameter _ _ _ (by ring) (mag j).1
  have he : t=fun _ => t 0 := by
    funext j
    linarith [ht j,ht 0]
  have hT : T=5*t 0+sigma := by
    change total t sigma=5*t 0+sigma
    rw [he]
    simp only [total]
    ring
  have hs := (Complex.normSq_nonneg (d (full false)))
  rw [ms0] at hs
  have forced := MainTheory.OrderFour25Pinning.forced (t 0) sigma T hT (ht 0) (mag 0).2 hs
  refine ⟨?_,forced.2.2⟩
  change t=fun _ => 1/16
  rw [he,forced.2.1]

end MainTheory.OrderFour25Forced
