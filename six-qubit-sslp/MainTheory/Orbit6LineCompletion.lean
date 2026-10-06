import MainTheory.Orbit6SpinorDisplays
set_option autoImplicit false
namespace MainTheory.Orbit6LineCompletion
open scoped BigOperators
open SixQubit.Orbit6 MainTheory.Orbit6MomentDisplays
open MainTheory.Orbit6PhysicalRowData MainTheory.Orbit6SpinorDisplays
noncomputable section

theorem wedge_zero_scalar (u v : Fin 2 → ℂ) (hu : u≠0) (hw : wedge u v=0) :
    ∃ t : ℂ,v=t • u := by
  change u 0*v 1-u 1*v 0=0 at hw
  by_cases h0 : u 0=0
  · have h1 : u 1≠0 := by
      intro h1
      apply hu
      funext i
      fin_cases i <;> assumption
    have hv0 : v 0=0 := by
      rw [h0,zero_mul,zero_sub,neg_eq_zero] at hw
      exact (mul_eq_zero.mp hw).resolve_left h1
    refine ⟨v 1/u 1,?_⟩
    funext i
    fin_cases i
    · change v 0=(v 1/u 1)*u 0
      simp only [h0,mul_zero]
      exact hv0
    · change v 1=(v 1/u 1)*u 1
      field_simp
  · refine ⟨v 0/u 0,?_⟩
    funext i
    fin_cases i
    · change v 0=(v 0/u 0)*u 0
      field_simp
    · change v 1=(v 0/u 0)*u 1
      field_simp
      linear_combination hw

theorem pairing_smul_right (u v : Fin 2 → ℂ) (t : ℂ) :
    pairing u (t • v)=t*pairing u v := by
  simp only [pairing,Pi.smul_apply,smul_eq_mul]
  ring

theorem pairing_smul_left (u v : Fin 2 → ℂ) (t : ℂ) :
    pairing (t • u) v=star t*pairing u v := by
  simp only [pairing,Pi.smul_apply,smul_eq_mul,star_mul']
  ring

theorem pairing_conjugate (u v : Fin 2 → ℂ) :
    star (pairing u v)=pairing v u := by
  simp only [pairing,star_add,star_mul',star_star]
  ring

theorem anchor_nonzero_of_data (c d : SS.State 6 ℂ) (h : RowData c d) : anchor c≠0 := by
  obtain ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,h37,h38,h39,h40,h41,h42,h43,h44,h45,h46⟩ := h
  intro hz
  have hz0 := congrFun hz 0
  have hz1 := congrFun hz 1
  change c y0=0 at hz0
  change c y11=0 at hz1
  norm_num [hz0,hz1] at h39

theorem line_of_data (c d : SS.State 6 ℂ) (h : RowData c d) :
    ∃ U : Submodule ℂ (Fin 2 → ℂ),Module.finrank ℂ U=1 ∧
      anchor c∈U ∧ (∀ i,topComplement d i∈U) ∧
      (∀ e w,w∈U → pairing w (bottomEdge c e)=0) ∧
      (∀ i w,w∈U → pairing w (topSingleton d i)=0) := by
  have hu := anchor_nonzero_of_data c d h
  obtain ⟨hb,ha,hc⟩ := aligned_rows_of_data c d h
  refine ⟨ℂ ∙ anchor c,finrank_span_singleton hu,Submodule.mem_span_singleton_self _,?_,?_,?_⟩
  · intro i
    obtain ⟨t,ht⟩ := wedge_zero_scalar (anchor c) (topComplement d i) hu (hc i)
    exact Submodule.mem_span_singleton.mpr ⟨t,ht.symm⟩
  · intro e w hw
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hw
    rw [← ht,pairing_smul_left]
    have hz := congrArg star (ha e)
    rw [pairing_conjugate,star_zero] at hz
    rw [hz,mul_zero]
  · intro i w hw
    obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hw
    rw [← ht,pairing_smul_left,hb i,mul_zero]

theorem edge_orthogonality_of_data (c d : SS.State 6 ℂ) (h : RowData c d)
    (e : Fin 10) (i : Fin 5) : pairing (bottomEdge c e) (topComplement d i)=0 := by
  obtain ⟨_,ha,hc⟩ := aligned_rows_of_data c d h
  obtain ⟨t,ht⟩ := wedge_zero_scalar (anchor c) (topComplement d i)
    (anchor_nonzero_of_data c d h) (hc i)
  rw [ht,pairing_smul_right,ha e,mul_zero]

theorem physical_lines (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∃ U : Submodule ℂ (Fin 2 → ℂ),Module.finrank ℂ U=1 ∧
      anchor c∈U ∧ (∀ i,topComplement d i∈U) ∧
      (∀ e w,w∈U → pairing w (bottomEdge c e)=0) ∧
      (∀ i w,w∈U → pairing w (topSingleton d i)=0) :=
  line_of_data c d (physical_row_data c d hc hd hnc hnd hkl)

theorem physical_edge_orthogonality (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (e : Fin 10) (i : Fin 5) :
    pairing (bottomEdge c e) (topComplement d i)=0 :=
  edge_orthogonality_of_data c d (physical_row_data c d hc hd hnc hnd hkl) e i

end
end MainTheory.Orbit6LineCompletion
