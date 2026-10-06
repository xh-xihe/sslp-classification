import MainTheory.ComplexSchmidtDecomposition
import MainTheory.Orbit5OffdiagonalDisplays
import Mathlib.LinearAlgebra.Matrix.Trace
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit5SchmidtCompletion
open scoped Matrix BigOperators
open MainTheory.ComplexSchmidtStep MainTheory.ComplexSchmidtDecomposition
open MainTheory.Orbit5Displays MainTheory.Orbit5OffdiagonalDisplays
open SixQubit.Orbit5 MainTheory.Orbit5PhysicalRowData
noncomputable section

theorem gram_trace_unitary (X L R : M2) (hL : unitary L) (hR : unitary R) :
    Matrix.trace ((L*X*R)*(L*X*R).conjTranspose)=Matrix.trace (X*X.conjTranspose) := by
  have he : (L*X*R)*(L*X*R).conjTranspose=L*(X*X.conjTranspose)*L.conjTranspose := by
    rw [Matrix.conjTranspose_mul,Matrix.conjTranspose_mul]
    calc
      (L*X*R)*(R.conjTranspose*(X.conjTranspose*L.conjTranspose))=
          L*X*(R*R.conjTranspose)*X.conjTranspose*L.conjTranspose := by noncomm_ring
      _=_ := by rw [hR.1,Matrix.mul_one];noncomm_ring
  rw [he,Matrix.trace_mul_cycle,hL.2,Matrix.one_mul]

theorem coefficient_gram_trace (x : Fin 4 → ℂ) :
    Matrix.trace (coefficientMatrix x*(coefficientMatrix x).conjTranspose)=
      (SixQubit.Trace5.nsq x : ℂ) := by
  simp only [Matrix.trace,Matrix.diag,Fin.sum_univ_two,Matrix.mul_apply,Matrix.conjTranspose_apply]
  change (x 0*star (x 0)+x 1*star (x 1))+(x 2*star (x 2)+x 3*star (x 3))=_
  simp only [SixQubit.Trace5.nsq,Complex.ofReal_add,Complex.normSq_eq_conj_mul_self,
    ← Complex.star_def]
  ring

theorem diagonal_gram_trace (s t : ℝ) :
    Matrix.trace ((Matrix.diagonal ![(s : ℂ),(t : ℂ)])*
      (Matrix.diagonal ![(s : ℂ),(t : ℂ)]).conjTranspose)=((s^2+t^2 : ℝ) : ℂ) := by
  norm_num [Matrix.trace,Fin.sum_univ_two,Matrix.mul_apply,Matrix.conjTranspose_apply,
    Matrix.diagonal,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Complex.star_def,Complex.conj_ofReal]
  ring

theorem normalized_schmidt (x : Fin 4 → ℂ) (hn : SixQubit.Trace5.nsq x=1/3) :
    ∃ L R : M2,∃ s t : ℝ,unitary L ∧ unitary R ∧ 0≤s ∧ 0≤t ∧ s^2+t^2=1 ∧
      L*coefficientMatrix x*R=schmidtMatrix (Real.sqrt 3)⁻¹ s t := by
  obtain ⟨L,R,s0,t0,hL,hR,hs0,ht0,hd⟩ := schmidt (coefficientMatrix x)
  have htrace := gram_trace_unitary (coefficientMatrix x) L R hL hR
  rw [hd,diagonal_gram_trace,coefficient_gram_trace,hn] at htrace
  have hnorm : s0^2+t0^2=1/3 := by exact_mod_cast htrace
  have hr : 0<Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : (Real.sqrt (3 : ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  refine ⟨L,R,Real.sqrt 3*s0,Real.sqrt 3*t0,hL,hR,mul_nonneg hr.le hs0,
    mul_nonneg hr.le ht0,?_,?_⟩
  · nlinarith [hnorm]
  · rw [hd]
    unfold schmidtMatrix
    have hs : (Real.sqrt 3)⁻¹*(Real.sqrt 3*s0)=s0 := by
      rw [← mul_assoc,inv_mul_cancel₀ hr.ne',one_mul]
    have ht : (Real.sqrt 3)⁻¹*(Real.sqrt 3*t0)=t0 := by
      rw [← mul_assoc,inv_mul_cancel₀ hr.ne',one_mul]
    rw [hs,ht]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

theorem physical_schmidt (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    ∃ L R : M2,∃ s t : ℝ,unitary L ∧ unitary R ∧ 0≤s ∧ 0≤t ∧ s^2+t^2=1 ∧
      L*coefficientMatrix (uu c)*R=schmidtMatrix (Real.sqrt 3)⁻¹ s t := by
  exact normalized_schmidt (uu c) (physical_row_data c d hc hd hnc hnd hkl).1

end
end MainTheory.Orbit5SchmidtCompletion
