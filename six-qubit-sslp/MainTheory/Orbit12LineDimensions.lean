import MainTheory.Orbit12ScalarCompletion
set_option autoImplicit false
namespace MainTheory.Orbit12LineDimensions
open SixQubit.Orbit12 MainTheory.Orbit12Frames MainTheory.Orbit12MomentDisplays
open MainTheory.Orbit12AnchorLines MainTheory.Orbit12AnchorScalars
noncomputable section

theorem span_pair_scalar (x y : Fin 2 → ℂ) (t : ℂ) (hy : y=t • x) :
    Submodule.span ℂ {x,y}=ℂ ∙ x := by
  have hm : y∈ℂ ∙ x := Submodule.mem_span_singleton.mpr ⟨t,hy.symm⟩
  rw [Set.pair_comm]
  exact Submodule.span_insert_eq_span hm

theorem actual_line_dimensions (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    Module.finrank ℂ (Submodule.span ℂ {u c,v c})=1 ∧
    Module.finrank ℂ (Submodule.span ℂ {ut d,vt d})=1 := by
  obtain ⟨⟨t,ht⟩,⟨s,hs⟩⟩ := actual_anchor_lines c d hc hd hnc hnd hkl
  have hu := bottom_zero_anchor _ _ (physical_moments c d hc hd hnc hnd hkl)
  have hU := top_zero_anchor _ _ (physical_moments c d hc hd hnc hnd hkl)
  have hun : u c≠0 := by
    intro hz
    have h0 := congrFun hz 0
    have h1 := congrFun hz 1
    change c y0=0 at h0
    change c y8=0 at h1
    change Complex.normSq (c y0)+Complex.normSq (c y8)=1/4 at hu
    norm_num [h0,h1] at hu
  have hUn : ut d≠0 := by
    intro hz
    have h0 := congrFun hz 0
    have h1 := congrFun hz 1
    change d z0=0 at h0
    change d z8=0 at h1
    change Complex.normSq (d z0)+Complex.normSq (d z8)=1/4 at hU
    norm_num [h0,h1] at hU
  rw [span_pair_scalar _ _ t ht,span_pair_scalar _ _ s hs]
  exact ⟨finrank_span_singleton hun,finrank_span_singleton hUn⟩
end
end MainTheory.Orbit12LineDimensions
