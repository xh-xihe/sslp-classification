import MainTheory.Orbit26PhysicalNorms
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit26PhysicalDependentAnchors
open scoped BigOperators Matrix
open MainTheory.Orbit26PhysicalNorms MainTheory.Orbit26PhysicalMatrices
open MainTheory.Orbit26DependentAnchors
open MainTheory.Orbit26PrintedProbabilities
open MainTheory.OrderFour26Moments (pattern)
open MainTheory.Orbit26 (M2)
open SixQubit.Orbit26 (S0 S1)
noncomputable section

theorem matrix_of_columns (A : M2) (lam : ℂ) (h : ∀ i,A i 1=lam*A i 0) :
    A=Matrix.vecMulVec (col A 0) ![1,lam] := by
  ext i j
  fin_cases j
  · simp [Matrix.vecMulVec_apply,col]
  · simpa [Matrix.vecMulVec_apply,col,mul_comm] using h i

theorem physical_anchor_vectors (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∃ lam mu : ℂ,Complex.normSq lam=1 ∧ Complex.normSq mu=1 ∧
      nsq (col (C c 3) 0)=1/8 ∧ nsq (col (D d 3) 0)=1/8 ∧
      C c 3=Matrix.vecMulVec (col (C c 3) 0) ![1,lam] ∧
      D d 3=Matrix.vecMulVec (col (D d 3) 0) ![1,mu] := by
  obtain ⟨hsC,hsD⟩ := physical_anchor_singular c d hc hd hnc hnd hkl
  obtain ⟨hp,hq⟩ := physical_probabilities c d hc hd hnc hnd hkl
  have hC (j : Fin 2) : nsq (col (C c 3) j)=1/8 :=
    (column_C c 3 j).trans (congrFun hp _ |>.trans (anchor_mass _ _ _ rfl j))
  have hD (j : Fin 2) : nsq (col (D d 3) j)=1/8 :=
    (column_D d 3 j).trans (congrFun hq _ |>.trans (anchor_mass _ _ _ rfl j))
  obtain ⟨lam,hl,hlc⟩ := phase_columns (C c 3) hsC (hC 0) (hC 1)
  obtain ⟨mu,hm,hmd⟩ := phase_columns (D d 3) hsD (hD 0) (hD 1)
  exact ⟨lam,mu,hl,hm,hC 0,hD 0,matrix_of_columns _ _ hlc,matrix_of_columns _ _ hmd⟩

theorem physical_anchor_projectors (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∃ cv dv : Vec,nsq cv=1 ∧ nsq dv=1 ∧
      C c 3*(C c 3)ᴴ=(1/4 : ℂ) • projector cv ∧
      D d 3*(D d 3)ᴴ=(1/4 : ℂ) • projector dv := by
  obtain ⟨hsC,hsD⟩ := physical_anchor_singular c d hc hd hnc hnd hkl
  obtain ⟨hC,hD⟩ := physical_column_masses c d hc hd hnc hnd hkl
  have hCn (j : Fin 2) : nsq (col (C c 3) j)=1/8 :=
    (hC 3 j).trans (anchor_mass _ _ _ rfl j)
  have hDn (j : Fin 2) : nsq (col (D d 3) j)=1/8 :=
    (hD 3 j).trans (anchor_mass _ _ _ rfl j)
  obtain ⟨cv,hcv,hCp⟩ := rank_one_anchor (C c 3) hsC (hCn 0) (hCn 1)
  obtain ⟨dv,hdv,hDp⟩ := rank_one_anchor (D d 3) hsD (hDn 0) (hDn 1)
  exact ⟨cv,dv,hcv,hdv,hCp,hDp⟩

theorem physical_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (lam mu : ℂ)
    (hC : C c 3=Matrix.vecMulVec (col (C c 3) 0) ![1,lam])
    (hD : D d 3=Matrix.vecMulVec (col (D d 3) 0) ![1,mu]) (g : Fin 3) :
    row (col (C c 3) 0) (D d g.castSucc)+
      star (row (col (D d 3) 0) (C c g.castSucc))=0 ∧
    star lam • row (col (C c 3) 0) (D d g.castSucc)+
      mu • star (row (col (D d 3) 0) (C c g.castSucc))=0 := by
  have he := physical_anchor c d hc hd hkl g
  rw [hC,hD] at he
  exact anchor_rows _ _ _ _ _ _ he

theorem physical_nonmatching_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (lam mu : ℂ) (hne : mu≠star lam)
    (hC : C c 3=Matrix.vecMulVec (col (C c 3) 0) ![1,lam])
    (hD : D d 3=Matrix.vecMulVec (col (D d 3) 0) ![1,mu]) (g : Fin 3) :
    row (col (C c 3) 0) (D d g.castSucc)=0 ∧
      row (col (D d 3) 0) (C c g.castSucc)=0 := by
  obtain ⟨h0,h1⟩ := physical_rows c d hc hd hkl lam mu hC hD g
  obtain ⟨hu,hv⟩ := nonmatching_rows _ _ lam mu hne h0 h1
  exact ⟨hu,star_eq_zero.mp hv⟩

theorem physical_rho_anchors (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (cv dv : Vec)
    (hC : C c 3*(C c 3)ᴴ=(1/4 : ℂ) • projector cv)
    (hD : D d 3*(D d 3)ᴴ=(1/4 : ℂ) • projector dv) :
    (∑ k : Fin 4,C c k*(C c k)ᴴ)=
      (1/2 : ℂ) • (projector cv+projector dv) := by
  ext i j
  have he := physical_moment c d hc hd hkl 3
  rw [hC,hD] at he
  have hij := congrArg (fun X => X i j) he
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] at hij ⊢
  linear_combination -2*hij
end
end MainTheory.Orbit26PhysicalDependentAnchors
