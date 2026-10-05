import MainTheory.Orbit26AnchorMatrix
import MainTheory.TwoSpinorStandardForm
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit26DependentAnchors
open scoped BigOperators Matrix
open MainTheory.Orbit26 (M2 cj Jmat)
noncomputable section
abbrev Vec := Fin 2 → ℂ
def nsq (v : Vec) : ℝ := ∑ i,Complex.normSq (v i)
def col (A : M2) (j : Fin 2) : Vec := fun i => A i j
def row (v : Vec) (A : M2) : Vec := star v ᵥ* A
def projector (v : Vec) : M2 := Matrix.vecMulVec v (star v)

theorem dependent_columns (A : M2) (hA : A.det=0) (h0 : 0<nsq (col A 0)) :
    ∃ lam : ℂ,∀ i,A i 1=lam*A i 0 := by
  have hd : A 0 0*A 1 1-A 0 1*A 1 0=0 := by
    simpa only [Matrix.det_fin_two] using hA
  by_cases ha : A 0 0=0
  · have hb : A 1 0≠0 := by
      intro hb
      norm_num [nsq,col,Fin.sum_univ_two,ha,hb] at h0
    refine ⟨A 1 1/A 1 0,?_⟩
    intro i
    fin_cases i
    · have hz : A 0 1=0 := by
        have he : A 0 1*A 1 0=0 := by linear_combination -hd + A 1 1*ha
        exact (mul_eq_zero.mp he).resolve_right hb
      simp [hz,ha]
    · simp [hb]
  · refine ⟨A 0 1/A 0 0,?_⟩
    intro i
    fin_cases i
    · simp [ha]
    · change A 1 1=A 0 1/A 0 0*A 1 0
      field_simp
      linear_combination hd

theorem phase_columns (A : M2) (hA : A.det=0)
    (h0 : nsq (col A 0)=1/8) (h1 : nsq (col A 1)=1/8) :
    ∃ lam : ℂ,Complex.normSq lam=1 ∧ ∀ i,A i 1=lam*A i 0 := by
  obtain ⟨lam,hl⟩ := dependent_columns A hA (by linarith)
  have he : nsq (col A 1)=Complex.normSq lam*nsq (col A 0) := by
    simp only [nsq,col,hl,map_mul,Finset.mul_sum]
  refine ⟨lam,?_,hl⟩
  rw [h0,h1] at he
  linarith

theorem gram_of_phase_columns (A : M2) (lam : ℂ) (hl : Complex.normSq lam=1)
    (hcol : ∀ i,A i 1=lam*A i 0) :
    A*Aᴴ=(2 : ℂ) • projector (col A 0) := by
  have hu : lam*star lam=1 := by
    rw [mul_comm,SixQubit.star_mul_self,hl]
    rfl
  ext i j
  simp only [Matrix.mul_apply,Matrix.conjTranspose_apply,Fin.sum_univ_two,hcol,
    projector,Matrix.vecMulVec_apply,col,Pi.star_apply,Matrix.smul_apply,smul_eq_mul]
  simp only [star_mul']
  linear_combination (A i 0*star (A j 0))*hu

theorem normalized_projector (v : Vec) (r : ℝ) (hr : 0<r) (hv : nsq v=r^2) :
    nsq (fun i => v i/(r : ℂ))=1 ∧
    projector v=(r^2 : ℂ) • projector (fun i => v i/(r : ℂ)) := by
  have hr0 : (r : ℂ)≠0 := by exact_mod_cast hr.ne'
  constructor
  · simp only [nsq,map_div₀,Complex.normSq_ofReal,← Finset.sum_div]
    rw [show ∑ i,Complex.normSq (v i)=r^2 from hv]
    field_simp
  · ext i j
    simp only [projector,Matrix.vecMulVec_apply,Pi.star_apply,Matrix.smul_apply,
      smul_eq_mul,star_div₀,Complex.star_def,Complex.conj_ofReal]
    field_simp

theorem rank_one_anchor (A : M2) (hA : A.det=0)
    (h0 : nsq (col A 0)=1/8) (h1 : nsq (col A 1)=1/8) :
    ∃ v : Vec,nsq v=1 ∧ A*Aᴴ=(1/4 : ℂ) • projector v := by
  obtain ⟨lam,hl,hcol⟩ := phase_columns A hA h0 h1
  let r : ℝ := Real.sqrt (1/8)
  have hr : 0<r := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : r^2=1/8 := Real.sq_sqrt (by norm_num)
  obtain ⟨hv,hproj⟩ := normalized_projector (col A 0) r hr (h0.trans hr2.symm)
  refine ⟨fun i => A i 0/(r : ℂ),hv,?_⟩
  rw [gram_of_phase_columns A lam hl hcol,hproj,smul_smul]
  have hrC : (r : ℂ)^2=1/8 := by
    have he := congrArg (fun x : ℝ => (x : ℂ)) hr2
    push_cast at he
    exact he
  norm_num [hrC,col]

theorem anchor_rows (c d : Vec) (lam mu : ℂ) (C D : M2)
    (h : (Matrix.vecMulVec c ![1,lam])ᴴ*D+
      (Cᴴ*Matrix.vecMulVec d ![1,mu]).transpose=0) :
    (star c ᵥ* D)+star (star d ᵥ* C)=0 ∧
    (star lam) • (star c ᵥ* D)+mu • star (star d ᵥ* C)=0 := by
  constructor
  · funext j
    have he := congrArg (fun X => X 0 j) h
    norm_num [Matrix.add_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.transpose_apply,Matrix.vecMulVec_apply,Fin.sum_univ_two,
      Pi.add_apply,Pi.zero_apply,Matrix.vecMul,dotProduct,Pi.star_apply,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] at he ⊢
    simp only [starRingEnd_apply] at he ⊢
    linear_combination he
  · funext j
    have he := congrArg (fun X => X 1 j) h
    norm_num [Matrix.add_apply,Matrix.mul_apply,Matrix.conjTranspose_apply,
      Matrix.transpose_apply,Matrix.vecMulVec_apply,Fin.sum_univ_two,
      Pi.add_apply,Pi.zero_apply,Matrix.vecMul,dotProduct,Pi.star_apply,
      Pi.smul_apply,smul_eq_mul,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at he ⊢
    simp only [starRingEnd_apply] at he ⊢
    linear_combination he

theorem nonmatching_rows (u v : Vec) (lam mu : ℂ) (hne : mu≠star lam)
    (h0 : u+v=0) (h1 : star lam • u+mu • v=0) : u=0 ∧ v=0 := by
  have hv : v=0 := by
    funext j
    have e0 := congrFun h0 j
    have e1 := congrFun h1 j
    norm_num [Pi.add_apply,Pi.smul_apply] at e0 e1
    simp only [starRingEnd_apply] at e1
    have he : (mu-star lam)*v j=0 := by
      linear_combination e1-star lam*e0
    exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hne)
  refine ⟨?_,hv⟩
  simpa [hv] using h0
end
end MainTheory.Orbit26DependentAnchors
