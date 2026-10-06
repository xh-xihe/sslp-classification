import MainTheory.Orbit26NormalizedRows
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit26NonmatchingPhysical
open scoped BigOperators Matrix
open MainTheory.Orbit26DependentAnchors MainTheory.Orbit26OrthogonalGram
open MainTheory.Orbit26NormalizedRows MainTheory.Orbit26PhysicalDependentAnchors
open MainTheory.Orbit26PhysicalMatrices MainTheory.Orbit26PhysicalNorms
open MainTheory.Orbit26PrintedProbabilities
open MainTheory.Orbit26 (M2)
open SixQubit.Orbit26 (S0 S1)
noncomputable section

theorem physical_normalized_data (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    nsq (unitAnchor (C c 3))=1 ∧ nsq (unitAnchor (D d 3))=1 ∧
    C c 3*(C c 3)ᴴ=(1/4 : ℂ) • projector (unitAnchor (C c 3)) ∧
    D d 3*(D d 3)ᴴ=(1/4 : ℂ) • projector (unitAnchor (D d 3)) ∧
    (∀ g,nsq (col (C c g) 0)+nsq (col (C c g) 1)=1/4) ∧
    (∀ g,nsq (col (D d g) 0)+nsq (col (D d g) 1)=1/4) := by
  obtain ⟨hsC,hsD⟩ := physical_anchor_singular c d hc hd hnc hnd hkl
  obtain ⟨hC,hD⟩ := physical_column_masses c d hc hd hnc hnd hkl
  have hCn (j : Fin 2) := (hC 3 j).trans (anchor_mass _ _ _ rfl j)
  have hDn (j : Fin 2) := (hD 3 j).trans (anchor_mass _ _ _ rfl j)
  obtain ⟨huC,hCp⟩ := normalized_anchor (C c 3) hsC (hCn 0) (hCn 1)
  obtain ⟨huD,hDp⟩ := normalized_anchor (D d 3) hsD (hDn 0) (hDn 1)
  refine ⟨huC,huD,hCp,hDp,?_,?_⟩
  · intro g
    rw [hC,hC]
    exact pair_mass _ _ _ rfl g
  · intro g
    rw [hD,hD]
    exact pair_mass _ _ _ rfl g

theorem normalized_zero_row (A B : M2) (h : row (col A 0) B=0) :
    row (unitAnchor A) B=0 := by
  change row (fun i => col A 0 i/(Real.sqrt (1/8 : ℝ) : ℂ)) B=0
  rw [row_div,h,smul_zero]

theorem physical_nonmatching_projectors (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (lam mu : ℂ) (hne : mu≠star lam)
    (hC : C c 3=Matrix.vecMulVec (col (C c 3) 0) ![1,lam])
    (hD : D d 3=Matrix.vecMulVec (col (D d 3) 0) ![1,mu]) :
    (∀ g : Fin 3,C c g.castSucc*(C c g.castSucc)ᴴ=
      (1/4 : ℂ) • (1-projector (unitAnchor (D d 3)))) ∧
    (∀ g : Fin 3,D d g.castSucc*(D d g.castSucc)ᴴ=
      (1/4 : ℂ) • (1-projector (unitAnchor (C c 3)))) ∧
    projector (unitAnchor (C c 3))+projector (unitAnchor (D d 3))=1 := by
  obtain ⟨huC,huD,hCp,hDp,hmC,hmD⟩ := physical_normalized_data c d hc hd hnc hnd hkl
  have hCg (g : Fin 3) : C c g.castSucc*(C c g.castSucc)ᴴ=
      (1/4 : ℂ) • (1-projector (unitAnchor (D d 3))) := by
    have hz := (physical_nonmatching_rows c d hc hd hkl lam mu hne hC hD g).2
    rw [orthogonal_gram _ _ huD (normalized_zero_row _ _ hz),hmC]
    norm_num
  have hDg (g : Fin 3) : D d g.castSucc*(D d g.castSucc)ᴴ=
      (1/4 : ℂ) • (1-projector (unitAnchor (C c 3))) := by
    have hz := (physical_nonmatching_rows c d hc hd hkl lam mu hne hC hD g).1
    rw [orthogonal_gram _ _ huC (normalized_zero_row _ _ hz),hmD]
    norm_num
  refine ⟨hCg,hDg,?_⟩
  have hC0 := hCg 0
  have hD0 := hDg 0
  change C c 0*(C c 0)ᴴ=(1/4 : ℂ) • (1-projector (unitAnchor (D d 3))) at hC0
  change D d 0*(D d 0)ᴴ=(1/4 : ℂ) • (1-projector (unitAnchor (C c 3))) at hD0
  have he := (physical_moment c d hc hd hkl 0).trans (physical_moment c d hc hd hkl 3).symm
  rw [hC0,hD0,hCp,hDp] at he
  ext i j
  have hij := congrArg (fun A => A i j) he
  simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul] at hij ⊢
  linear_combination -2*hij

theorem physical_nonmatching_impossible (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (lam mu : ℂ) (hne : mu≠star lam)
    (hC : C c 3=Matrix.vecMulVec (col (C c 3) 0) ![1,lam])
    (hD : D d 3=Matrix.vecMulVec (col (D d 3) 0) ![1,mu]) : False := by
  obtain ⟨hCg,hDg,hp⟩ := physical_nonmatching_projectors c d hc hd hnc hnd hkl lam mu hne hC hD
  obtain ⟨huC,huD,hCp,hDp,_,_⟩ := physical_normalized_data c d hc hd hnc hnd hkl
  have heq : projector (unitAnchor (C c 3))=projector (unitAnchor (D d 3)) := by
    have hC0 := hCg 0
    have hC1 := hCg 1
    have hC2 := hCg 2
    have hD0 := hDg 0
    have hD1 := hDg 1
    have hD2 := hDg 2
    change C c 0*(C c 0)ᴴ=(1/4 : ℂ) • (1-projector (unitAnchor (D d 3))) at hC0
    change C c 1*(C c 1)ᴴ=(1/4 : ℂ) • (1-projector (unitAnchor (D d 3))) at hC1
    change C c 2*(C c 2)ᴴ=(1/4 : ℂ) • (1-projector (unitAnchor (D d 3))) at hC2
    change D d 0*(D d 0)ᴴ=(1/4 : ℂ) • (1-projector (unitAnchor (C c 3))) at hD0
    change D d 1*(D d 1)ᴴ=(1/4 : ℂ) • (1-projector (unitAnchor (C c 3))) at hD1
    change D d 2*(D d 2)ᴴ=(1/4 : ℂ) • (1-projector (unitAnchor (C c 3))) at hD2
    have hr := physical_rho c d hc hd hkl
    rw [Fin.sum_univ_four,Fin.sum_univ_four,hC0,hC1,hC2,hD0,hD1,hD2,hCp,hDp] at hr
    ext i j
    have hij := congrArg (fun A => A i j) hr
    simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.sub_apply,smul_eq_mul] at hij ⊢
    linear_combination hij
  have ho := projector_orthogonality _ _ huC hp
  have hx := congrArg (fun A : M2 => star (unitAnchor (C c 3)) ⬝ᵥ A *ᵥ unitAnchor (C c 3)) heq
  dsimp only at hx
  rw [projector_qform,projector_qform,ho] at hx
  have hself : star (unitAnchor (C c 3)) ⬝ᵥ unitAnchor (C c 3)=1 := by
    simp only [dotProduct,Fin.sum_univ_two,Pi.star_apply]
    rw [SixQubit.star_mul_self,SixQubit.star_mul_self,← Complex.ofReal_add]
    simpa [nsq,Fin.sum_univ_two] using congrArg (fun x : ℝ => (x : ℂ)) huC
  rw [hself] at hx
  norm_num at hx
end
end MainTheory.Orbit26NonmatchingPhysical
