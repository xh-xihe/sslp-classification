import MainTheory.Orbit26NonmatchingPhysical
set_option autoImplicit false
set_option maxHeartbeats 12000000
namespace MainTheory.Orbit26MatchingRows
open scoped BigOperators Matrix
open MainTheory.Orbit26DependentAnchors MainTheory.Orbit26NormalizedRows
open MainTheory.Orbit26 (M2 Jmat)
noncomputable section

theorem normalized_row_relation (v w : Vec) (A B : M2) (r : ℝ)
    (h : row v B+star (row w A)=0) :
    row (fun i => v i/(r : ℂ)) B=-star (row (fun i => w i/(r : ℂ)) A) := by
  rw [row_div,row_div]
  funext j
  have hj := congrFun h j
  norm_num [Pi.add_apply] at hj
  simp only [Pi.smul_apply,smul_eq_mul,Pi.neg_apply,Pi.star_apply,star_mul',
    star_div₀,star_one,Complex.star_def,Complex.conj_ofReal]
  simp only [starRingEnd_apply] at hj ⊢
  linear_combination (1/(r : ℂ))*hj

theorem contract_outer (v w : Vec) (A B F G : M2) :
    v ⬝ᵥ (MainTheory.Orbit26.cj A*Jmat*G.transpose+
      MainTheory.Orbit26.cj B*Jmat*F.transpose) *ᵥ star w=
      star (row v A) ⬝ᵥ Jmat *ᵥ row w G+
      star (row v B) ⬝ᵥ Jmat *ᵥ row w F := by
  simp only [row,Matrix.vecMul,Matrix.mulVec,dotProduct,Fin.sum_univ_two,
    Matrix.add_apply,Matrix.mul_apply,Matrix.transpose_apply,Pi.star_apply,
    MainTheory.Orbit26.cj_apply,star_add,star_mul',Complex.star_def]
  simp only [starRingEnd_apply,star_star]
  ring

theorem J_rows (v w : Vec) (A B F G : M2)
    (h : MainTheory.Orbit26.cj A*Jmat*G.transpose+
      MainTheory.Orbit26.cj B*Jmat*F.transpose=0)
    (hF : row w F=-star (row v A)) (hG : row w G=-star (row v B)) :
    SixQubit.Block26.Jform (row v A 0) (row v A 1) (row v B 0) (row v B 1)=0 := by
  have he := congrArg (fun M : M2 => v ⬝ᵥ M *ᵥ star w) h
  dsimp only at he
  rw [contract_outer,hF,hG,Matrix.zero_mulVec,dotProduct_zero] at he
  have hs := congrArg star he
  norm_num [Jmat,Matrix.mulVec,dotProduct,Fin.sum_univ_two,Pi.star_apply,
    Pi.neg_apply,SixQubit.Block26.Jform] at hs ⊢
  linear_combination -hs/2

theorem row_sum (A : Fin 3 → M2) (C3 D3 : M2) (cv dv : Vec)
    (hv : nsq dv=1)
    (hC : C3*C3ᴴ=(1/4 : ℂ) • projector cv)
    (hD : D3*D3ᴴ=(1/4 : ℂ) • projector dv)
    (hm : (∑ g,A g*(A g)ᴴ)=C3*C3ᴴ+(2 : ℂ) • (D3*D3ᴴ)) :
    (∑ g,nsq (row dv (A g)))=1/2+Complex.normSq (star cv ⬝ᵥ dv)/4 := by
  have he := congrArg (fun M : M2 => star dv ⬝ᵥ M *ᵥ dv) hm
  dsimp only at he
  rw [Fin.sum_univ_three,Matrix.add_mulVec,Matrix.add_mulVec,dotProduct_add,
    dotProduct_add,hC,hD,Matrix.add_mulVec,dotProduct_add,
    Matrix.smul_mulVec,dotProduct_smul,Matrix.smul_mulVec,dotProduct_smul,
    Matrix.smul_mulVec,dotProduct_smul,
    smul_smul,projector_qform,projector_qform] at he
  have hself : star dv ⬝ᵥ dv=1 := by
    simp only [dotProduct,Fin.sum_univ_two,Pi.star_apply]
    rw [SixQubit.star_mul_self,SixQubit.star_mul_self,← Complex.ofReal_add]
    simpa [nsq,Fin.sum_univ_two] using congrArg (fun x : ℝ => (x : ℂ)) hv
  rw [hself,← row_qform,← row_qform,← row_qform] at he
  have hre := congrArg Complex.re he
  norm_num [Fin.sum_univ_three] at hre ⊢
  linarith
end
end MainTheory.Orbit26MatchingRows
