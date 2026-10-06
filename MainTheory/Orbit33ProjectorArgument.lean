import MainTheory.Orbit33NormalizedPairs
import MainTheory.Orbit33PhysicalReflection

/-! The literal projector argument following the six-block reflection.
Intermediate projector identities use only the indicated norms and relations.
-/
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit33ProjectorArgument
open MainTheory.Orbit33PrintedBlocks MainTheory.Orbit33NormalizedPairs
open scoped BigOperators Matrix
noncomputable section

theorem scaled_outer (u w : Fin 2 → ℂ) (a : ℂ) (r : ℝ)
    (hu : normSq u=1) (hw : normSq w=r) (hf : w=a • u) :
    outer w=(r : ℂ) • outer u := by
  have hs := square_cast u
  have ht := square_cast w
  rw [hu] at hs
  rw [hw,hf] at ht
  norm_num [square,star_mul'] at hs ht
  have ha : a*star a=(r : ℂ) := by
    conv_lhs => norm_num
    linear_combination ht-(a*(starRingEnd ℂ) a)*hs
  ext i j
  rw [hf]
  norm_num [outer,star_mul'] at ha ⊢
  linear_combination (u i*(starRingEnd ℂ) (u j))*ha

theorem orthogonal_outer (v w : Fin 2 → ℂ) (r : ℝ)
    (hv : normSq v=1) (hw : normSq w=r) (hi : inner w v=0) :
    outer w=(r : ℂ) • (1-outer v) := by
  have hs := square_cast v
  have ht := square_cast w
  rw [hv] at hs
  rw [hw] at ht
  obtain ⟨h0,h1,h2⟩ := SixQubit.Block33.ortho2 (w 0) (w 1) (v 0) (v 1) hi
  norm_num [square] at hs ht
  norm_num at h0 h1 h2
  have hd0 : w 0*star (w 0)=(r : ℂ)*(v 1*star (v 1)) := by
    norm_num
    linear_combination h0-(w 0*(starRingEnd ℂ) (w 0))*hs+(v 1*(starRingEnd ℂ) (v 1))*ht
  have hd1 : w 1*star (w 1)=(r : ℂ)*(v 0*star (v 0)) := by
    norm_num
    linear_combination h2-(w 1*(starRingEnd ℂ) (w 1))*hs+(v 0*(starRingEnd ℂ) (v 0))*ht
  have ho : w 0*star (w 1)=-(r : ℂ)*(v 0*star (v 1)) := by
    norm_num
    linear_combination h1-(w 0*(starRingEnd ℂ) (w 1))*hs-(v 0*(starRingEnd ℂ) (v 1))*ht
  have hor := congrArg star ho
  norm_num [star_mul'] at hd0 hd1 ho hor
  ext i j
  fin_cases i <;> fin_cases j
  · norm_num [outer]
    linear_combination hd0+(r : ℂ)*hs
  · norm_num [outer]
    linear_combination ho
  · norm_num [outer]
    linear_combination hor
  · norm_num [outer]
    linear_combination hd1+(r : ℂ)*hs

theorem cancel_scalar {A B : Matrix (Fin 2) (Fin 2) ℂ} (r : ℝ) (hr : r≠0)
    (h : (r : ℂ) • A=(r : ℂ) • B) : A=B := by
  ext i j
  have he := congrFun (congrFun h i) j
  exact mul_left_cancel₀ (by exact_mod_cast hr) he

theorem projector_sums (u v : Fin 2 → ℂ) (rho : Matrix (Fin 2) (Fin 2) ℂ)
    (hnear : outer u+outer v=(2 : ℂ) • rho)
    (hfar : (1-outer v)+(1-outer u)=(2 : ℂ) • rho) :
    outer u+outer v=1 ∧ rho=(1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  constructor
  · ext i j
    have h0 := congrFun (congrFun hnear i) j
    have h1 := congrFun (congrFun hfar i) j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul] at h0 h1 ⊢
    linear_combination (1/2 : ℂ)*h0-(1/2 : ℂ)*h1
  · ext i j
    have h0 := congrFun (congrFun hnear i) j
    have h1 := congrFun (congrFun hfar i) j
    simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul] at h0 h1 ⊢
    linear_combination -(1/4 : ℂ)*h0-(1/4 : ℂ)*h1

theorem physical_near_and_far_sums (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit33.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit33.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (f : Frame c d) :
    outer f.u+outer f.v=(2 : ℂ) • rho c ∧
      (1-outer f.v)+(1-outer f.u)=(2 : ℂ) • rho c := by
  have hn := (physical_norms_and_reflection c d hc hd hnc hnd hkl).1
  have hm := (physical_norms_and_reflection c d hc hd hnc hnd hkl).2
  have hu0 : outer (CBlock c 0)=((3/10 : ℝ) : ℂ) • outer f.u := by
    apply scaled_outer f.u _ (f.a 0) (3/10) f.unitU _ _
    · simpa [normSq,Fin.sum_univ_two,R] using (hn 0).1
    · simpa [near] using (f.factors 0).2.2.1
  have hv0 : outer (DBlock d 0)=((3/10 : ℝ) : ℂ) • outer f.v := by
    apply scaled_outer f.v _ (f.b 0) (3/10) f.unitV _ _
    · simpa [normSq,Fin.sum_univ_two,R] using (hn 0).2
    · simpa [near] using (f.factors 0).2.2.2
  have hu3 : outer (CBlock c ⟨3,by decide⟩)=((1/10 : ℝ) : ℂ) • (1-outer f.v) := by
    apply orthogonal_outer f.v _ (1/10) f.unitV _ _
    · simpa [normSq,Fin.sum_univ_two,R] using (hn ⟨3,by decide⟩).1
    · simpa [far] using (f.orthogonalFar 0).1
  have hv3 : outer (DBlock d ⟨3,by decide⟩)=((1/10 : ℝ) : ℂ) • (1-outer f.u) := by
    apply orthogonal_outer f.u _ (1/10) f.unitU _ _
    · simpa [normSq,Fin.sum_univ_two,R] using (hn ⟨3,by decide⟩).2
    · have he := congrArg star (f.orthogonalFar 0).2
      norm_num [MainTheory.Orbit33NormalizedPairs.inner,far,star_mul'] at he ⊢
      linear_combination he
  constructor
  · apply cancel_scalar (3/10) (by norm_num)
    have he := hm 0
    rw [hu0,hv0] at he
    norm_num [R] at he
    ext i j
    have h0 := congrFun (congrFun he i) j
    norm_num [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] at h0 ⊢
    linear_combination (10/3 : ℂ)*h0
  · apply cancel_scalar (1/10) (by norm_num)
    have he := hm ⟨3,by decide⟩
    rw [hu3,hv3] at he
    norm_num [R] at he
    ext i j
    have h0 := congrFun (congrFun he i) j
    norm_num [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] at h0 ⊢
    linear_combination (10 : ℂ)*h0

theorem physical_projector_sums (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit33.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit33.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (f : Frame c d) :
    outer f.u+outer f.v=1 ∧ rho c=(1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have he := physical_near_and_far_sums c d hc hd hnc hnd hkl f
  exact projector_sums f.u f.v (rho c) he.1 he.2

theorem physical_all_bottom_outers (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit33.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit33.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (f : Frame c d) :
    ∀ i, outer (CBlock c i)=(R i : ℂ) • outer f.u := by
  have hn := (physical_norms_and_reflection c d hc hd hnc hnd hkl).1
  have hp := (physical_projector_sums c d hc hd hnc hnd hkl f).1
  have hcomp : (1 : Matrix (Fin 2) (Fin 2) ℂ)-outer f.v=outer f.u := by
    rw [← hp]
    abel
  have hn0 : ∀ i : Fin 3, outer (CBlock c (near i))=(R (near i) : ℂ) • outer f.u := by
    intro i
    apply scaled_outer f.u _ (f.a i) _ f.unitU _ (f.factors i).2.2.1
    simpa [normSq,Fin.sum_univ_two] using (hn (near i)).1
  have hf0 : ∀ j : Fin 3, outer (CBlock c (far j))=(R (far j) : ℂ) • outer f.u := by
    intro j
    rw [← hcomp]
    apply orthogonal_outer f.v _ _ f.unitV _ (f.orthogonalFar j).1
    simpa [normSq,Fin.sum_univ_two] using (hn (far j)).1
  intro i
  fin_cases i
  · exact hn0 ⟨0,by decide⟩
  · exact hn0 ⟨1,by decide⟩
  · exact hn0 ⟨2,by decide⟩
  · exact hf0 ⟨0,by decide⟩
  · exact hf0 ⟨1,by decide⟩
  · exact hf0 ⟨2,by decide⟩

theorem physical_rho_projector (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit33.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit33.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (f : Frame c d) : rho c=outer f.u := by
  have he := physical_all_bottom_outers c d hc hd hnc hnd hkl f
  unfold rho
  simp_rw [he]
  rw [← Finset.sum_smul]
  have hR : (∑ i : Fin 6, (R i : ℂ))=1 := by norm_num [R,Fin.sum_univ_succ,Fin.succ]
  rw [hR,one_smul]

theorem unit_projectors_orthogonal (u v : Fin 2 → ℂ) (hu : normSq u=1)
    (hp : outer u+outer v=1) : MainTheory.Orbit33NormalizedPairs.inner u v=0 := by
  have h00 := congrFun (congrFun hp 0) 0
  have h01 := congrFun (congrFun hp 0) 1
  have h10 := congrFun (congrFun hp 1) 0
  have h11 := congrFun (congrFun hp 1) 1
  have hs := square_cast u
  rw [hu] at hs
  norm_num [outer,square] at h00 h01 h10 h11 hs
  have hz : MainTheory.Orbit33NormalizedPairs.inner u v *
      star (MainTheory.Orbit33NormalizedPairs.inner u v)=0 := by
    conv_lhs => norm_num [MainTheory.Orbit33NormalizedPairs.inner,star_mul']
    linear_combination (u 0*(starRingEnd ℂ) (u 0))*h00+
      ((starRingEnd ℂ) (u 0)*u 1)*h01+((starRingEnd ℂ) (u 1)*u 0)*h10+
      (u 1*(starRingEnd ℂ) (u 1))*h11-
      (u 0*(starRingEnd ℂ) (u 0)+u 1*(starRingEnd ℂ) (u 1))*hs
  rcases mul_eq_zero.mp hz with h | h
  · exact h
  · exact star_eq_zero.1 h

theorem physical_unit_orthogonality (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit33.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit33.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (f : Frame c d) :
    MainTheory.Orbit33NormalizedPairs.inner f.u f.v=0 :=
  unit_projectors_orthogonal f.u f.v f.unitU
    (physical_projector_sums c d hc hd hnc hnd hkl f).1

theorem rank_one_not_half (u : Fin 2 → ℂ) :
    outer u≠(1/2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  intro h
  have hd : Matrix.det (outer u)=0 := by
    simp only [Matrix.det_fin_two,outer]
    ring
  rw [h] at hd
  norm_num [Matrix.det_fin_two] at hd

theorem physical_no_go (c d : SS.State 6 ℂ)
    (hc : ∀ x, x ∉ SixQubit.Orbit33.S0 → c x=0)
    (hd : ∀ x, x ∉ SixQubit.Orbit33.S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) : False := by
  obtain ⟨f⟩ := physical_frame c d hc hd hnc hnd hkl
  have hP := physical_rho_projector c d hc hd hnc hnd hkl f
  have hH := (physical_projector_sums c d hc hd hnc hnd hkl f).2
  exact rank_one_not_half f.u (hP.symm.trans hH)

end
end MainTheory.Orbit33ProjectorArgument
