import MainTheory.Orbit26DependentAnchors
import Mathlib.Analysis.Matrix.Spectrum
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.ComplexSchmidtStep
open scoped Matrix BigOperators
open MainTheory.TwoSpinorNormalization MainTheory.Orbit26DependentAnchors
noncomputable section

abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ
def unitary (R : M2) : Prop := R*R.conjTranspose=1 ∧ R.conjTranspose*R=1
theorem unitary_transpose (R : M2) (h : unitary R) : unitary R.transpose := by
  constructor
  · have hh := congrArg Matrix.transpose h.2
    simpa only [Matrix.transpose_mul,Matrix.transpose_conjTranspose,Matrix.transpose_one] using hh
  · have hh := congrArg Matrix.transpose h.1
    simpa only [Matrix.transpose_mul,Matrix.transpose_conjTranspose,Matrix.transpose_one] using hh

theorem unitary_mul (R S : M2) (hR : unitary R) (hS : unitary S) : unitary (R*S) := by
  constructor
  · rw [Matrix.conjTranspose_mul]
    calc
      (R*S)*(S.conjTranspose*R.conjTranspose)=R*(S*S.conjTranspose)*R.conjTranspose := by noncomm_ring
      _=1 := by rw [hS.1,Matrix.mul_one,hR.1]
  · rw [Matrix.conjTranspose_mul]
    calc
      (S.conjTranspose*R.conjTranspose)*(R*S)=S.conjTranspose*(R.conjTranspose*R)*S := by noncomm_ring
      _=1 := by rw [hR.2,Matrix.mul_one,hS.2]

def rowNorm (Y : M2) (i : Fin 2) := nsq (Y i)
def rightBasis (Y : M2) (r : ℝ) : M2 :=
  (basisMatrix (fun j => Y 0 j/(r : ℂ))).transpose

theorem right_basis_coordinates (Y : M2) (r : ℝ) (hr : 0<r)
    (hn : rowNorm Y 0=r^2)
    (ho : star (Y 0 0)*Y 1 0+star (Y 0 1)*Y 1 1=0) :
    unitary (rightBasis Y r) ∧ (Y*rightBasis Y r) 0 0=(r : ℂ) ∧
      (Y*rightBasis Y r) 0 1=0 ∧ (Y*rightBasis Y r) 1 0=0 := by
  have hrc : (r : ℂ)≠0 := by exact_mod_cast hr.ne'
  have hn' : nsq (fun j => Y 0 j/(r : ℂ))=1 :=
    (normalized_projector (Y 0) r hr hn).1
  have hu : Complex.normSq (Y 0 0/(r : ℂ))+Complex.normSq (Y 0 1/(r : ℂ))=1 := by
    simpa only [nsq,Fin.sum_univ_two] using hn'
  have hQ := basis_unitary (fun j => Y 0 j/(r : ℂ)) hu
  have hQt := unitary_transpose _ ⟨hQ,mul_eq_one_comm.mp hQ⟩
  refine ⟨hQt,?_,?_,?_⟩
  · have hh := congrArg (fun x : ℝ => (x : ℂ)) hn
    simp only [rowNorm,nsq,Fin.sum_univ_two] at hh
    push_cast at hh
    simp only [Complex.normSq_eq_conj_mul_self,← Complex.star_def] at hh
    simp only [rightBasis,basisMatrix,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      Fin.sum_univ_two,star_div₀,Complex.star_def,Complex.conj_ofReal]
    simp only [Complex.star_def] at hh
    field_simp
    linear_combination hh
  · simp only [rightBasis,basisMatrix,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      Fin.sum_univ_two]
    field_simp
    ring
  · simp only [rightBasis,basisMatrix,Matrix.mul_apply,Matrix.transpose_apply,
      Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
      Fin.sum_univ_two,star_div₀,Complex.star_def,Complex.conj_ofReal]
    simp only [Complex.star_def] at ho
    field_simp
    linear_combination ho

theorem orthogonal_rows_positive (Y : M2) (hpos : 0<rowNorm Y 0)
    (ho : star (Y 0 0)*Y 1 0+star (Y 0 1)*Y 1 1=0) :
    ∃ R : M2,∃ s t : ℝ,unitary R ∧ 0≤s ∧ 0≤t ∧
      Y*R=Matrix.diagonal ![(s : ℂ),(t : ℂ)] := by
  let r : ℝ := Real.sqrt (rowNorm Y 0)
  have hr : 0<r := Real.sqrt_pos.mpr hpos
  have hr2 : r^2=rowNorm Y 0 := Real.sq_sqrt (le_of_lt hpos)
  obtain ⟨hR,h00,h01,h10⟩ := right_basis_coordinates Y r hr hr2.symm ho
  let Z : M2 := Y*rightBasis Y r
  obtain ⟨a,ha,haw⟩ := exists_phase_correction (Z 1 1)
  let D : M2 := Matrix.diagonal ![1,a]
  have hD : unitary D := by
    have hh := diagonal_unitary 1 a (by norm_num) ha
    exact ⟨hh,mul_eq_one_comm.mp hh⟩
  refine ⟨rightBasis Y r*D,r,‖Z 1 1‖,unitary_mul _ _ hR hD,
    le_of_lt hr,norm_nonneg _,?_⟩
  rw [← Matrix.mul_assoc]
  change Z*D=Matrix.diagonal ![(r : ℂ),(‖Z 1 1‖ : ℂ)]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp only [Matrix.mul_apply,Fin.sum_univ_two,D,Matrix.diagonal]
  · change Z 0 0*1+Z 0 1*0=(r : ℂ)
    simp only [Z,h00,h01,mul_one,mul_zero,add_zero]
  · change Z 0 0*0+Z 0 1*a=0
    simp only [Z,h01,mul_zero,zero_mul,zero_add]
  · change Z 1 0*1+Z 1 1*0=0
    simp only [Z,h10,mul_one,mul_zero,add_zero]
  · change Z 1 0*0+Z 1 1*a=(‖Z 1 1‖ : ℂ)
    rw [mul_zero,zero_add,mul_comm]
    exact haw

end
end MainTheory.ComplexSchmidtStep
