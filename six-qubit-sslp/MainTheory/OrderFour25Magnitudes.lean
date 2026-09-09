import MainTheory.OrderFour25Forced
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace MainTheory.OrderFour25Magnitudes
open MainTheory.OrderFour25Support MainTheory.OrderFour25Moments
open MainTheory.OrderFour25CoordinateMoments MainTheory.MomentPolytope
open SixQubit.Orbit25 (S0 S1)

theorem forced_values :
    (∀ b,bot (fun _ => 1/16) (3/16) (ai b)=3/16 ∧
      up (fun _ => 1/16) (3/16) (si b)=3/16) ∧
    (∀ b j,bot (fun _ => 1/16) (3/16) (bi b j)=1/16 ∧
      up (fun _ => 1/16) (3/16) (ri b j)=1/16) := by
  have v := coordinate_values (fun _ => 1/16) (3/16)
  norm_num [total] at v
  constructor
  · intro b
    cases b
    · exact ⟨v.1,v.2.2.1⟩
    · exact ⟨v.2.1,v.2.2.2.1⟩
  · intro b j
    cases b
    · exact ⟨(v.2.2.2.2 j).1,(v.2.2.2.2 j).2.2.1⟩
    · exact ⟨(v.2.2.2.2 j).2.1,(v.2.2.2.2 j).2.2.2⟩

theorem actual (c d : SS.State 6 ℂ) (p : Sum (Fin 12) (Fin 12) → ℝ)
    (H : Feasible bottom top p)
    (hnc : ∀ i,Complex.normSq (c (bottom i))=p (Sum.inl i))
    (hnd : ∀ i,Complex.normSq (d (top i))=p (Sum.inr i))
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∀ b,Complex.normSq (c (anchor b))=3/16 ∧ Complex.normSq (d (full b))=3/16) ∧
    (∀ b j,Complex.normSq (c (hat b j))=1/16 ∧ Complex.normSq (d (tail b j))=1/16) := by
  obtain ⟨ht,hs⟩ := MainTheory.OrderFour25Forced.parameters_forced c d p H hnc hnd hc hd hkl
  have hp := probabilities p H
  rw [ht,hs] at hp
  have hb : ∀ i,Complex.normSq (c (bottom i))=bot (fun _ => 1/16) (3/16) i :=
    fun i => (hnc i).trans (congrFun hp.1 i)
  have hu : ∀ i,Complex.normSq (d (top i))=up (fun _ => 1/16) (3/16) i :=
    fun i => (hnd i).trans (congrFun hp.2 i)
  constructor
  · intro b
    rw [anchor_index,full_index,hb,hu]
    exact forced_values.1 b
  · intro b j
    rw [hat_index,tail_index,hb,hu]
    exact forced_values.2 b j
end MainTheory.OrderFour25Magnitudes
