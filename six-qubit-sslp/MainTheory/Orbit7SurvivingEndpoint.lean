import SixQubit.Orbit7FullSupportTarget

set_option autoImplicit false

namespace MainTheory.Orbit7SurvivingEndpoint

open SixQubit.Orbit7Universal

theorem physical_endpoint (c d : SS.State 6 ℂ)
    (hc : ∀ x,SS.weight uniformAv x ≠ 0 → c x=0)
    (hd : ∀ x,SS.weight uniformAv x ≠ 2 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hcode : SS.HasDistance ![c,d] 3)
    (hfull : FullEdgeSupport (xcoord c d)) (hind : extremeDet c d ≠ 0)
    (hC : anchorC c d ≠ 0) (r q : Fin 5 → ℂ) (mu nu : ℂ)
    (haff : AffineTangentData c d r q mu nu)
    (s : Fin 5) (R : ℂ) (hR : ∀ i,i ≠ s → r i=R) :
    star (anchorC c d)*(R+r s)+anchorD c d=0 := by
  have pdata := physical_full_tangent_data c d hc hd hnc hnd hcode hfull
  have hv := (scalar_normal_form c d hc hd hnc hnd hcode).2.1
  have hD : anchorD c d ≠ 0 := by
    intro hz
    apply hind
    unfold anchorD at hz
    unfold extremeDet
    linear_combination (1/6 : ℂ)*hz
  obtain ⟨hstar,hnon⟩ := exceptional_edge_sum_partition r s R hR
  rcases exceptional_three_cases c d hc hd hnc hnd hcode hfull hind hC
    r q mu nu haff s R hR with he | he | he
  · exact (exceptional_equal_values_impossible c d hv pdata hD r s
      (R+r s) (2*R) haff.y_vertex hstar hnon he).elim
  · exact he
  · exact (nonincident_anchor_endpoint_impossible c d hc hd hnc hnd hcode
      r s (2*R) haff.y_vertex hnon hD he).elim

theorem normalized_endpoint (C D T : ℂ) (c d : ℝ)
    (hC : C=(c : ℂ)) (hD : D=(d : ℂ)) (hc : c ≠ 0)
    (h : star C*T+D=0) : T=-(d : ℂ)/(c : ℂ) := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [hC,hD] at h
  simp at h
  apply (eq_div_iff hcC).mpr
  linear_combination h

end MainTheory.Orbit7SurvivingEndpoint
