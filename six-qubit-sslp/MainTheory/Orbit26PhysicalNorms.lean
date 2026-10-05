import MainTheory.Orbit26PhysicalMatrices
import MainTheory.Orbit26DependentAnchors
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit26PhysicalNorms
open scoped BigOperators Matrix
open MainTheory.Orbit26PhysicalMatrices
open MainTheory.Orbit26DependentAnchors
open MainTheory.Orbit26PrintedProbabilities
open MainTheory.OrderFour26Moments (pattern)
open MainTheory.Orbit26 (M2 cj)
open SixQubit.Orbit26 (S0 S1)
open MainTheory.OrderFour26Support (bottomAt topAt tailWords)
noncomputable section

theorem column_C (c : SS.State 6 ℂ) (g : Fin 4) (j : Fin 2) :
    nsq (col (C c g) j)=P c (groupIndex g j) := by
  simp [nsq,col,C,P,Fin.sum_univ_two]

theorem column_D (d : SS.State 6 ℂ) (g : Fin 4) (j : Fin 2) :
    nsq (col (D d g) j)=Q d (groupIndex g j) := by
  simp [nsq,col,D,Q,Fin.sum_univ_two]

theorem row_component_bound (A : M2) (v : Vec) (hv : nsq v=1) (j : Fin 2) :
    Complex.normSq ((v ᵥ* cj A) j)≤nsq (col A j) := by
  have hu : Complex.normSq (star (v 0))+Complex.normSq (star (v 1))=1 := by
    simpa [nsq,Fin.sum_univ_two] using hv
  have he := SixQubit.Block26.cauchy_schwarz_unit
    (star (v 0)) (star (v 1)) (star (A 0 j)) (star (A 1 j)) hu
  simpa [SixQubit.Block26.ip,cj,Matrix.vecMul,dotProduct,Fin.sum_univ_two,
    nsq,col] using he

theorem row_total_bound (A : M2) (v : Vec) (hv : nsq v=1) :
    nsq (v ᵥ* cj A)≤nsq (col A 0)+nsq (col A 1) := by
  have h0 := row_component_bound A v hv 0
  have h1 := row_component_bound A v hv 1
  rw [nsq,Fin.sum_univ_two]
  linarith

theorem pair_mass (p : Fin 8 → ℝ) (a b : ℝ) (hp : p=pattern a b) (g : Fin 4) :
    p (groupIndex g 0)+p (groupIndex g 1)=1/4 := by
  rw [hp]
  fin_cases g
  all_goals norm_num [groupIndex,pattern]
  all_goals ring

theorem anchor_mass (p : Fin 8 → ℝ) (a b : ℝ) (hp : p=pattern a b) (j : Fin 2) :
    p (groupIndex 3 j)=1/8 := by
  rw [hp]
  fin_cases j <;> norm_num [groupIndex,pattern]

theorem group_nonzero (A : Fin 4 → M2) (p : Fin 8 → ℝ) (a b : ℝ)
    (hc : ∀ g j,nsq (col (A g) j)=p (groupIndex g j)) (hp : p=pattern a b) :
    ∀ g,A g≠0 := by
  intro g hz
  have he : nsq (col (A g) 0)+nsq (col (A g) 1)=1/4 := by
    rw [hc,hc]
    exact pair_mass p a b hp g
  rw [hz] at he
  norm_num [nsq,col] at he

theorem some_full_group (A : Fin 4 → M2) (p : Fin 8 → ℝ) (a b : ℝ)
    (hc : ∀ g j,nsq (col (A g) j)=p (groupIndex g j)) (hp : p=pattern a b) :
    ∃ g : Fin 3,¬(A g.castSucc 0 0=0 ∧ A g.castSucc 1 0=0) ∧
      ¬(A g.castSucc 0 1=0 ∧ A g.castSucc 1 1=0) := by
  classical
  by_contra h
  push_neg at h
  have he (g : Fin 3) :
      (A g.castSucc 0 0=0 ∧ A g.castSucc 1 0=0) ∨
      (A g.castSucc 0 1=0 ∧ A g.castSucc 1 1=0) := by
    have hg := h g
    tauto
  have hz (g : Fin 4) (j : Fin 2) (h0 : A g 0 j=0 ∧ A g 1 j=0) :
      p (groupIndex g j)=0 := by
    rw [← hc]
    simp [nsq,col,Fin.sum_univ_two,h0.1,h0.2]
  rcases he 0 with h0|h0 <;> rcases he 1 with h1|h1 <;> rcases he 2 with h2|h2
  all_goals first | have e0 := hz 0 0 h0 | have e0 := hz 0 1 h0
  all_goals first | have e1 := hz 1 0 h1 | have e1 := hz 1 1 h1
  all_goals first | have e2 := hz 2 0 h2 | have e2 := hz 2 1 h2
  all_goals rw [hp] at e0 e1 e2
  all_goals norm_num [groupIndex,pattern] at e0 e1 e2
  all_goals linarith

theorem physical_column_masses (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∀ g j,nsq (col (C c g) j)=pattern (P c 3) (P c 5) (groupIndex g j)) ∧
    (∀ g j,nsq (col (D d g) j)=pattern (P c 3) (P c 5) (groupIndex g j)) := by
  obtain ⟨hp,hq⟩ := physical_probabilities c d hc hd hnc hnd hkl
  exact ⟨fun g j => (column_C c g j).trans (congrFun hp _),
    fun g j => (column_D d g j).trans (congrFun hq _)⟩
theorem group_row_bound (A : Fin 4 → M2) (p : Fin 8 → ℝ) (a b : ℝ)
    (hc : ∀ g j,nsq (col (A g) j)=p (groupIndex g j)) (hp : p=pattern a b)
    (v : Vec) (hv : nsq v=1) (g : Fin 4) :
    nsq (v ᵥ* cj (A g))≤1/4 := by
  have he := row_total_bound (A g) v hv
  rw [hc,hc,pair_mass p a b hp g] at he
  exact he

theorem axis_bound (A : Fin 4 → M2) (p : Fin 8 → ℝ) (a b : ℝ)
    (hc : ∀ g j,nsq (col (A g) j)=p (groupIndex g j)) (hp : p=pattern a b)
    (v : Vec) (hv : nsq v=1) (j : Fin 2) :
    Complex.normSq ((v ᵥ* cj (A 0)) j)+Complex.normSq ((v ᵥ* cj (A 1)) j)+
      Complex.normSq ((v ᵥ* cj (A 2)) j)≤3/8 := by
  have h0 := row_component_bound (A 0) v hv j
  have h1 := row_component_bound (A 1) v hv j
  have h2 := row_component_bound (A 2) v hv j
  rw [hc,hp] at h0 h1 h2
  fin_cases j
  all_goals norm_num [groupIndex,pattern] at h0 h1 h2 ⊢
  all_goals linarith

theorem physical_nonanchor_moment_C (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∑ g : Fin 3,C c g.castSucc*(C c g.castSucc)ᴴ)=
      C c 3*(C c 3)ᴴ+(2 : ℂ) • (D d 3*(D d 3)ᴴ) := by
  ext i j
  have he := congrArg (fun X => X i j) (physical_moment c d hc hd hkl 3)
  norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.add_apply,Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
    bottomAt,topAt,tailWords] at he ⊢
  linear_combination -2*he

theorem physical_nonanchor_moment_D (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    (∑ g : Fin 3,D d g.castSucc*(D d g.castSucc)ᴴ)=
      D d 3*(D d 3)ᴴ+(2 : ℂ) • (C c 3*(C c 3)ᴴ) := by
  ext i j
  have he := congrArg (fun X => X i j) (physical_moment c d hc hd hkl 3)
  have hr := congrArg (fun X => X i j) (physical_rho c d hc hd hkl)
  norm_num [C,D,groupIndex,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.add_apply,Matrix.smul_apply,Matrix.sum_apply,Fin.sum_univ_succ,Fin.succ,
    bottomAt,topAt,tailWords] at he hr ⊢
  linear_combination -2*he-hr

theorem physical_anchor_singular (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    (C c 3).det=0 ∧ (D d 3).det=0 := by
  obtain ⟨hp,hq⟩ := physical_probabilities c d hc hd hnc hnd hkl
  let a := P c 3
  let b := P c 5
  have hC := column_C c
  have hD := column_D d
  have hCn := group_nonzero (C c) (P c) a b hC hp
  have hDn := group_nonzero (D d) (Q d) a b hD hq
  have hrC : ¬IsUnit (C c 3).det → ∃ v : Vec,
      nsq v=1 ∧ C c 3*(C c 3)ᴴ=(1/4 : ℂ) • projector v := by
    intro hs
    have hz : (C c 3).det=0 := by simpa only [isUnit_iff_ne_zero,not_not] using hs
    exact rank_one_anchor (C c 3) hz
      ((hC 3 0).trans (anchor_mass (P c) a b hp 0))
      ((hC 3 1).trans (anchor_mass (P c) a b hp 1))
  have hrD : ¬IsUnit (D d 3).det → ∃ v : Vec,
      nsq v=1 ∧ D d 3*(D d 3)ᴴ=(1/4 : ℂ) • projector v := by
    intro hs
    have hz : (D d 3).det=0 := by simpa only [isUnit_iff_ne_zero,not_not] using hs
    exact rank_one_anchor (D d 3) hz
      ((hD 3 0).trans (anchor_mass (Q d) a b hq 0))
      ((hD 3 1).trans (anchor_mass (Q d) a b hq 1))
  have hout : ∀ g h : Fin 3,g≠h →
      cj (C c g.castSucc)*MainTheory.Orbit26.Jmat*(D d h.castSucc).transpose+
      cj (C c h.castSucc)*MainTheory.Orbit26.Jmat*(D d g.castSucc).transpose=0 := by
    intro g h hne
    rcases lt_or_gt_of_ne hne with hlt|hgt
    · exact physical_outer c d hc hd hkl g h hlt
    · simpa only [add_comm] using physical_outer c d hc hd hkl h g hgt
  have hs := MainTheory.Orbit26.anchor_singular
    (physical_anchor c d hc hd hkl) hout
    (physical_nonanchor_moment_C c d hc hd hkl)
    (physical_nonanchor_moment_D c d hc hd hkl)
    (fun g => hCn g.castSucc) (fun g => hDn g.castSucc)
    (some_full_group (C c) (P c) a b hC hp)
    (some_full_group (D d) (Q d) a b hD hq) hrD hrC
    (fun w hw g => by simpa only [nsq,Fin.sum_univ_two] using
      (group_row_bound (C c) (P c) a b hC hp w hw g.castSucc))
    (fun w hw g => by simpa only [nsq,Fin.sum_univ_two] using
      (group_row_bound (D d) (Q d) a b hD hq w hw g.castSucc))
    (fun w hw j => axis_bound (C c) (P c) a b hC hp w hw j)
    (fun w hw j => axis_bound (D d) (Q d) a b hD hq w hw j)
  simpa only [isUnit_iff_ne_zero,not_not] using hs
end
end MainTheory.Orbit26PhysicalNorms
