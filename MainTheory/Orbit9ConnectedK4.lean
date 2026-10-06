import MainTheory.Orbit9ComponentDisplays

set_option autoImplicit false

namespace MainTheory.Orbit9ConnectedK4

open SixQubit.Orbit9Universal MainTheory.Orbit9ConnectedComponents

theorem component_of_edge (c d : SS.State 6 ℂ) (H : FullKL c d)
    (a b : Fin 6) (hab : (graph c).Adj a b) :
    ∃ k l,component c a={a,b,k,l} ∧ (component c a).card=4 := by
  classical
  obtain ⟨k,l,hK⟩ := active_edge_has_actual_k4 c d H a b hab.1 hab.2.1 hab.2.2.1 hab.2.2.2
  let T : Finset (Fin 6) := {a,b,k,l}
  have closed (u v : Fin 6) (hu : u ∈ T) (huv : (graph c).Adj u v) : v ∈ T := by
    by_contra hv
    have hn : v ≠ a ∧ v ≠ b ∧ v ≠ k ∧ v ≠ l := by simpa [T] using hv
    have hz := hK.isolated v hn.1 hn.2.1 hn.2.2.1 hn.2.2.2 huv.2.2.1
    have hu' : u=a ∨ u=b ∨ u=k ∨ u=l := by simpa [T] using hu
    rcases hu' with rfl | rfl | rfl | rfl
    · exact huv.2.2.2 hz.1
    · exact huv.2.2.2 hz.2.1
    · exact huv.2.2.2 hz.2.2.1
    · exact huv.2.2.2 hz.2.2.2
  have he : component c a=T := by
    ext i
    constructor
    · intro hi
      have hr : (graph c).Reachable a i := (Finset.mem_filter.mp hi).2
      have ht := ((graph c).reachable_iff_reflTransGen a i).mp hr
      clear hi hr
      induction ht with
      | refl => simp [T]
      | @tail u v _ hadj ih => exact closed u v ih hadj
    · intro hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      have hi' : i=a ∨ i=b ∨ i=k ∨ i=l := by simpa [T] using hi
      rcases hi' with rfl | rfl | rfl | rfl
      · exact SimpleGraph.Reachable.rfl
      · exact hab.reachable
      · apply SimpleGraph.Adj.reachable
        exact ⟨hK.hik,hK.active_i,hK.active_k,hK.edge_ik⟩
      · apply SimpleGraph.Adj.reachable
        exact ⟨hK.hil,hK.active_i,hK.active_l,hK.edge_il⟩
  refine ⟨k,l,he,?_⟩
  rw [he]
  simp [T,hK.hij,hK.hik,hK.hil,hK.hjk,hK.hjl,hK.hkl]

theorem component_card (c d : SS.State 6 ℂ) (H : FullKL c d) (a : Fin 6) :
    (component c a).card=1 ∨ (component c a).card=4 := by
  classical
  by_cases hn : ∃ b,(graph c).Adj a b
  · obtain ⟨b,hb⟩ := hn
    obtain ⟨k,l,_,hc⟩ := component_of_edge c d H a b hb
    exact Or.inr hc
  · left
    have he : component c a={a} := by
      ext i
      constructor
      · intro hi
        have hr : (graph c).Reachable a i := (Finset.mem_filter.mp hi).2
        obtain ⟨w⟩ := hr
        cases w with
        | nil => simp
        | cons hadj _ => exact (hn ⟨_,hadj⟩).elim
      · intro hi
        have he : i=a := Finset.mem_singleton.mp hi
        subst i
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,SimpleGraph.Reachable.refl a⟩
    rw [he,Finset.card_singleton]

end MainTheory.Orbit9ConnectedK4
