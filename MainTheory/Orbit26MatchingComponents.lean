import MainTheory.Orbit26MatchingPhysical
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.Orbit26MatchingComponents
open scoped BigOperators Matrix
open MainTheory.Orbit26DependentAnchors MainTheory.Orbit26NormalizedRows
open MainTheory.Orbit26MatchingPhysical MainTheory.Orbit26NonmatchingPhysical
open MainTheory.Orbit26PhysicalMatrices MainTheory.Orbit26MatchingRows
open MainTheory.Orbit26OrthogonalGram
open MainTheory.Orbit26 (M2 cj Jmat)
open SixQubit.Orbit26 (S0 S1)
noncomputable section

theorem nsq_zero (v : Vec) (h : nsq v=0) : v=0 := by
  have hs : Complex.normSq (v 0)+Complex.normSq (v 1)=0 := by
    simpa [nsq,Fin.sum_univ_two] using h
  have h0 : v 0=0 := Complex.normSq_eq_zero.mp (by
    linarith [Complex.normSq_nonneg (v 0),Complex.normSq_nonneg (v 1)])
  have h1 : v 1=0 := Complex.normSq_eq_zero.mp (by
    linarith [Complex.normSq_nonneg (v 0),Complex.normSq_nonneg (v 1)])
  funext i
  fin_cases i
  · exact h0
  · exact h1

theorem row_norm_decomposition (v w : Vec) (A : M2) (h : projector v+projector w=1) :
    nsq (row v A)+nsq (row w A)=nsq (col A 0)+nsq (col A 1) := by
  have e00 := congrArg (fun M : M2 => M 0 0) h
  have e01 := congrArg (fun M : M2 => M 0 1) h
  have e10 := congrArg (fun M : M2 => M 1 0) h
  have e11 := congrArg (fun M : M2 => M 1 1) h
  have he : ((nsq (row v A)+nsq (row w A) : ℝ) : ℂ)=
      ((nsq (col A 0)+nsq (col A 1) : ℝ) : ℂ) := by
    norm_num [projector,Matrix.vecMulVec_apply,Matrix.add_apply,Pi.star_apply,
      Matrix.one_apply,nsq,col,row,Matrix.vecMul,dotProduct,Fin.sum_univ_two,
      Complex.normSq_eq_conj_mul_self,Complex.star_def] at e00 e01 e10 e11 ⊢
    simp only [starRingEnd_apply] at e00 e01 e10 e11 ⊢
    linear_combination (star (A 0 0)*A 0 0+star (A 0 1)*A 0 1)*e00+
      (star (A 0 0)*A 1 0+star (A 0 1)*A 1 1)*e01+
      (star (A 1 0)*A 0 0+star (A 1 1)*A 0 1)*e10+
      (star (A 1 0)*A 1 0+star (A 1 1)*A 1 1)*e11
  exact_mod_cast he

theorem complementary_row_zero (v w : Vec) (A : M2)
    (h : projector v+projector w=1)
    (hm : nsq (row w A)=nsq (col A 0)+nsq (col A 1)) : row v A=0 := by
  have he := row_norm_decomposition v w A h
  apply nsq_zero
  linarith

theorem physical_anchor_basis (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (lam mu : ℂ)
    (hC : C c 3=Matrix.vecMulVec (col (C c 3) 0) ![1,lam])
    (hD : D d 3=Matrix.vecMulVec (col (D d 3) 0) ![1,mu]) :
    projector (unitAnchor (C c 3))+projector (unitAnchor (D d 3))=1 := by
  obtain ⟨hv,hw,_,_,_,_⟩ := physical_normalized_data c d hc hd hnc hnd hkl
  have ho := physical_anchor_orthogonal c d hc hd hnc hnd hkl lam mu hC hD
  have hp := orthogonal_projector _ _ hv ho
  rw [hw,Complex.ofReal_one,one_smul] at hp
  rw [hp]
  abel

theorem mixed_J_rows (v w : Vec) (A B F G : M2)
    (he : cj A*Jmat*G.transpose+cj B*Jmat*F.transpose=0)
    (hz : row v B=0) (hg : row v G=-star (row w B)) :
    SixQubit.Block26.Jform (row v A 0) (row v A 1) (row w B 0) (row w B 1)=0 := by
  have ht := congrArg (fun M : M2 => v ⬝ᵥ M *ᵥ star v) he
  dsimp only at ht
  rw [contract_outer,hz,hg,Matrix.zero_mulVec,dotProduct_zero] at ht
  have hs := congrArg star ht
  norm_num [Jmat,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Pi.star_apply,
    Pi.neg_apply,SixQubit.Block26.Jform] at hs ⊢
  linear_combination -hs

theorem physical_mixed_J_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (lam mu : ℂ)
    (hC : C c 3=Matrix.vecMulVec (col (C c 3) 0) ![1,lam])
    (hD : D d 3=Matrix.vecMulVec (col (D d 3) 0) ![1,mu])
    (k g : Fin 3) (hkg : k≠g)
    (hf : nsq (row (unitAnchor (D d 3)) (C c g.castSucc))=1/4) :
    SixQubit.Block26.Jform
      (row (unitAnchor (C c 3)) (C c k.castSucc) 0)
      (row (unitAnchor (C c 3)) (C c k.castSucc) 1)
      (row (unitAnchor (D d 3)) (C c g.castSucc) 0)
      (row (unitAnchor (D d 3)) (C c g.castSucc) 1)=0 := by
  have hp := physical_anchor_basis c d hc hd hnc hnd hkl lam mu hC hD
  obtain ⟨_,_,_,_,hm,_⟩ := physical_normalized_data c d hc hd hnc hnd hkl
  have hz := complementary_row_zero _ _ (C c g.castSucc) hp (hf.trans (hm g.castSucc).symm)
  have he : cj (C c k.castSucc)*Jmat*(D d g.castSucc).transpose+
      cj (C c g.castSucc)*Jmat*(D d k.castSucc).transpose=0 := by
    rcases lt_or_gt_of_ne hkg with h|h
    · exact physical_outer c d hc hd hkl k g h
    · simpa only [add_comm] using physical_outer c d hc hd hkl g k h
  exact mixed_J_rows _ _ _ _ _ _ he hz
    (physical_firstrowD c d hc hd hkl lam mu hC hD g)
end
end MainTheory.Orbit26MatchingComponents
