import MainTheory.Orbit26OrthogonalGram
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit26NormalizedRows
open scoped BigOperators Matrix
open MainTheory.Orbit26DependentAnchors MainTheory.Orbit26OrthogonalGram
open MainTheory.Orbit26 (M2 cj)
noncomputable section
def unitAnchor (A : M2) : Vec := fun i => A i 0/(Real.sqrt (1/8 : ℝ) : ℂ)

theorem normalized_anchor (A : M2) (hA : A.det=0)
    (h0 : nsq (col A 0)=1/8) (h1 : nsq (col A 1)=1/8) :
    nsq (unitAnchor A)=1 ∧ A*Aᴴ=(1/4 : ℂ) • projector (unitAnchor A) := by
  obtain ⟨lam,hl,hcol⟩ := phase_columns A hA h0 h1
  let r : ℝ := Real.sqrt (1/8)
  have hr : 0<r := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : r^2=1/8 := Real.sq_sqrt (by norm_num)
  obtain ⟨hv,hp⟩ := normalized_projector (col A 0) r hr (h0.trans hr2.symm)
  refine ⟨hv,?_⟩
  rw [gram_of_phase_columns A lam hl hcol,hp,smul_smul]
  have hrC : (r : ℂ)^2=1/8 := by
    have he := congrArg (fun x : ℝ => (x : ℂ)) hr2
    push_cast at he
    exact he
  change ((2 : ℂ)*(r : ℂ)^2) • projector (unitAnchor A)=
    (1/4 : ℂ) • projector (unitAnchor A)
  rw [hrC]
  norm_num

theorem row_div (v : Vec) (r : ℝ) (A : M2) :
    row (fun i => v i/(r : ℂ)) A=(1/(r : ℂ)) • row v A := by
  funext j
  simp only [row,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Pi.star_apply,
    Pi.smul_apply,smul_eq_mul,star_div₀,Complex.star_def,Complex.conj_ofReal]
  ring

theorem conjugate_row (v : Vec) (A : M2) : star (row v A)=v ᵥ* cj A := by
  funext j
  simp only [row,Matrix.vecMul,dotProduct,Fin.sum_univ_two,Pi.star_apply,
    cj,Matrix.transpose_apply,Matrix.conjTranspose_apply,star_add,star_mul',star_star]

theorem row_nsq (v : Vec) (A : M2) : nsq (row v A)=nsq (v ᵥ* cj A) := by
  rw [← conjugate_row]
  simp [nsq]

theorem row_qform (v : Vec) (A : M2) :
    (nsq (row v A) : ℂ)=star v ⬝ᵥ (A*Aᴴ) *ᵥ v := by
  rw [row_nsq,nsq,Fin.sum_univ_two]
  exact MainTheory.Orbit26.rowNormSq_eq A v

theorem projector_qform (v w : Vec) :
    star v ⬝ᵥ (projector w) *ᵥ v=(Complex.normSq (star w ⬝ᵥ v) : ℂ) := by
  simp only [projector,Matrix.vecMulVec_apply,Matrix.mulVec,dotProduct,
    Pi.star_apply,Fin.sum_univ_two,Complex.normSq_eq_conj_mul_self,Complex.star_def,
    map_add,map_mul,Complex.conj_conj]
  ring

theorem projector_orthogonality (v w : Vec) (hv : nsq v=1)
    (h : projector v+projector w=1) : star w ⬝ᵥ v=0 := by
  have he := congrArg (fun A : M2 => star v ⬝ᵥ A *ᵥ v) h
  dsimp only at he
  rw [Matrix.add_mulVec,dotProduct_add,projector_qform,projector_qform,
    Matrix.one_mulVec] at he
  have huv : star v ⬝ᵥ v=1 := by
    simp only [dotProduct,Fin.sum_univ_two,Pi.star_apply]
    rw [SixQubit.star_mul_self,SixQubit.star_mul_self,← Complex.ofReal_add]
    simpa [nsq,Fin.sum_univ_two] using congrArg (fun x : ℝ => (x : ℂ)) hv
  rw [huv] at he
  norm_num at he
  simpa [dotProduct,Fin.sum_univ_two] using he
end
end MainTheory.Orbit26NormalizedRows
