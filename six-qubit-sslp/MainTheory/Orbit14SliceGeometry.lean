import MainTheory.WeightedLineFrames
import MainTheory.Orbit6LineCompletion
import SixQubit.ParityFour
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit14SliceGeometry
open scoped Matrix BigOperators
open MainTheory.Orbit26DependentAnchors
open MainTheory.Orbit26OrthogonalGram
noncomputable section

theorem nsq_nonneg (v : Vec) : 0≤nsq v := Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (v i))
theorem nsq_zero (v : Vec) (h : nsq v=0) : v=0 := by
  simp only [nsq,Fin.sum_univ_two] at h
  funext i
  apply Complex.normSq_eq_zero.mp
  fin_cases i
  · change Complex.normSq (v 0)=0
    nlinarith [Complex.normSq_nonneg (v 0),Complex.normSq_nonneg (v 1)]
  · change Complex.normSq (v 1)=0
    nlinarith [Complex.normSq_nonneg (v 0),Complex.normSq_nonneg (v 1)]

theorem positive_common_neighbor (p q : Fin 4 → ℝ) (mu : ℝ)
    (hp : ∀ k,0≤p k) (hq : ∀ k,0≤q k) (hs : (∑ k,q k)=mu)
    (hb : ∀ k,p k+q k=mu/2) (i j : Fin 4) (hij : i≠j) (hi : 0<p i) :
    ∃ k,k≠i ∧ k≠j ∧ 0<q k := by
  by_contra h
  have hz : ∀ k,k≠i → k≠j → q k=0 := by
    intro k hki hkj
    have hn : ¬0<q k := by
      intro hk
      exact h ⟨k,hki,hkj,hk⟩
    exact le_antisymm (le_of_not_gt hn) (hq k)
  have h0 := hb 0;have h1 := hb 1;have h2 := hb 2;have h3 := hb 3
  have hq0 := hq 0;have hq1 := hq 1;have hq2 := hq 2;have hq3 := hq 3
  have hpj := hp j
  fin_cases i <;> fin_cases j <;> norm_num at hij
  all_goals have hz0 := hz 0;have hz1 := hz 1;have hz2 := hz 2;have hz3 := hz 3
  all_goals norm_num [Fin.ext_iff] at hz0 hz1 hz2 hz3 hi hpj
  all_goals norm_num [Fin.sum_univ_succ,Fin.succ] at hs
  all_goals change q 0+(q 1+(q 2+q 3))=mu at hs
  all_goals linarith!

theorem common_orthogonal_wedge (u v w : Vec) (hw : 0<nsq w)
    (hu : star u ⬝ᵥ w=0) (hv : star v ⬝ᵥ w=0) :
    u 0*v 1-u 1*v 0=0 := by
  simp only [dotProduct,Fin.sum_univ_two,Pi.star_apply] at hu hv
  have h1 := congrArg star hu;have h2 := congrArg star hv
  simp only [star_add,star_mul,star_star,star_zero] at h1 h2
  have h1' : star (w 0)*u 0+star (w 1)*u 1=0 := by linear_combination h1
  have h2' : star (w 0)*v 0+star (w 1)*v 1=0 := by linear_combination h2
  have h := SixQubit.ParityFour.prop_wedge h1' h2'
  have he : w 0*star (w 0)+w 1*star (w 1)=(nsq w : ℂ) := by
    simp only [nsq,Fin.sum_univ_two,Complex.ofReal_add,
      Complex.normSq_eq_conj_mul_self,← Complex.star_def]
    ring
  rw [he] at h
  exact (mul_eq_zero.mp h).resolve_left (by exact_mod_cast hw.ne')

theorem balanced_slice_frames (c d : Fin 4 → Vec) (mu : ℝ) (hmu : 0 < mu)
    (hmc : (∑ i,nsq (c i))=mu) (hmd : (∑ i,nsq (d i))=mu)
    (hb : ∀ i,nsq (c i)+nsq (d i)=mu/2)
    (ho : ∀ i j,i≠j → star (c i) ⬝ᵥ d j=0) :
    ∃ v : Vec,nsq v=1 ∧ Module.finrank ℂ (ℂ ∙ v)=1 ∧
      (∀ i,∃ t : ℂ,c i=t • v) ∧ (∀ j,star v ⬝ᵥ d j=0) ∧
      (∑ i,projector (c i))=(mu : ℂ) • projector v ∧
      (∑ j,projector (d j))=(mu : ℂ) • (1-projector v) := by
  have hc0 : ∃ i,0<nsq (c i) := by
    by_contra h
    have hz : ∀ i,nsq (c i)=0 := by
      intro i
      have hn : ¬0<nsq (c i) := fun hi => h ⟨i,hi⟩
      exact le_antisymm (le_of_not_gt hn) (nsq_nonneg _)
    simp only [hz,Finset.sum_const_zero] at hmc
    linarith
  obtain ⟨i0,hi0⟩ := hc0
  have hcne : c i0≠0 := by
    intro h
    rw [h] at hi0
    norm_num [nsq] at hi0
  have hlines : ∀ i,∃ t : ℂ,c i=t • c i0 := by
    intro i
    by_cases he : i0=i
    · subst i
      exact ⟨1,(one_smul ℂ _).symm⟩
    obtain ⟨k,hk0,hki,hkp⟩ := positive_common_neighbor
      (fun j => nsq (c j)) (fun j => nsq (d j)) mu
      (fun j => nsq_nonneg _) (fun j => nsq_nonneg _) hmd hb i0 i he hi0
    exact MainTheory.Orbit6LineCompletion.wedge_zero_scalar _ _ hcne
      (common_orthogonal_wedge _ _ _ hkp (ho i0 k hk0.symm) (ho i k hki.symm))
  let r : ℝ := Real.sqrt (nsq (c i0))
  have hr : 0<r := Real.sqrt_pos.mpr hi0
  have hrc : (r : ℂ)≠0 := by exact_mod_cast hr.ne'
  let v : Vec := fun a => c i0 a/(r : ℂ)
  have hv : nsq v=1 := (normalized_projector (c i0) r hr (Real.sq_sqrt hi0.le).symm).1
  have hbase : c i0=(r : ℂ) • v := by
    funext a
    change c i0 a=(r : ℂ)*(c i0 a/(r : ℂ))
    field_simp [hrc]
  have hvne : v≠0 := by
    intro he
    rw [he] at hv
    norm_num [nsq] at hv
  have hcv : ∀ i,∃ t : ℂ,c i=t • v := by
    intro i
    obtain ⟨t,ht⟩ := hlines i
    refine ⟨t*(r : ℂ),?_⟩
    rw [ht,hbase,mul_smul]
  have hdv : ∀ j,star v ⬝ᵥ d j=0 := by
    intro j
    have hmass : 0<(∑ i,if i=j then 0 else nsq (c i)) := by
      have he : (∑ i,if i=j then 0 else nsq (c i))+nsq (c j)=mu := by
        rw [← hmc]
        have hx : ∀ i,(if i=j then 0 else nsq (c i))+(if i=j then nsq (c i) else 0)=nsq (c i) := by
          intro i;split_ifs <;> simp
        have hh := Finset.sum_congr rfl (fun i (_ : i∈Finset.univ) => hx i)
        simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hh
      have hh := hb j
      nlinarith [nsq_nonneg (d j)]
    have hp : ∃ i,i≠j ∧ 0<nsq (c i) := by
      by_contra h
      have hz : ∀ i,(if i=j then 0 else nsq (c i))=0 := by
        intro i
        split_ifs with he
        · rfl
        · exact le_antisymm (le_of_not_gt (fun hi => h ⟨i,he,hi⟩)) (nsq_nonneg _)
      simp only [hz,Finset.sum_const_zero] at hmass
      exact lt_irrefl _ hmass
    obtain ⟨i,hij,hip⟩ := hp
    obtain ⟨t,ht⟩ := hcv i
    have htne : t≠0 := by
      intro he
      rw [ht,he,zero_smul] at hip
      norm_num [nsq] at hip
    have he := ho i j hij
    rw [ht] at he
    simp only [dotProduct,Pi.star_apply,Pi.smul_apply,smul_eq_mul,star_mul',
      ← Finset.mul_sum,mul_assoc] at he
    exact (mul_eq_zero.mp he).resolve_left (star_ne_zero.mpr htne)
  refine ⟨v,hv,finrank_span_singleton hvne,hcv,hdv,
    MainTheory.WeightedLineFrames.line_frame_of_membership v c mu hv hcv hmc,?_⟩
  simp_rw [orthogonal_projector v _ hv (hdv _)]
  rw [← Finset.sum_smul]
  have hs : (∑ j,(nsq (d j) : ℂ))=(mu : ℂ) := by exact_mod_cast hmd
  rw [hs]

end
end MainTheory.Orbit14SliceGeometry
