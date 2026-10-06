import MainTheory.Orbit5MatrixRows
set_option autoImplicit false
namespace MainTheory.Orbit5OffdiagonalDisplays
open scoped Matrix BigOperators
open SixQubit.Orbit5 SixQubit.Trace5 MainTheory.Orbit5Displays MainTheory.Orbit5MatrixRows
noncomputable section

theorem traceSecond_adjoint (x y : Fin 4 → ℂ) :
    (traceSecond x y).conjTranspose=traceSecond y x := by
  ext r t
  simp only [traceSecond,Matrix.conjTranspose_apply,Fin.sum_univ_two,
    star_add,star_mul',star_star]
  ring

theorem traceFirst_adjoint (x y : Fin 4 → ℂ) :
    (traceFirst x y).conjTranspose=traceFirst y x := by
  ext r t
  simp only [traceFirst,Matrix.conjTranspose_apply,Fin.sum_univ_two,
    star_add,star_mul',star_star]
  ring

def PartialTraceRows (U A B : Matrix (Fin 2) (Fin 2) ℂ) : Prop :=
  U*B.conjTranspose+A*U.conjTranspose=0 ∧
  U.transpose*B.map star+A.transpose*U.map star=0

theorem physical_partial_trace_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (hvu : vv d=uu c) (i : Fin 4) :
    PartialTraceRows (coefficientMatrix (uu c))
      (coefficientMatrix (bottomVector c i)) (coefficientMatrix (topVector d i)) := by
  obtain ⟨h1,h2⟩ := physical_cross_matrices c d hc hd hnc hnd hkl i
  simp only [firstCross,secondCross,hvu] at h1 h2
  have h1a := congrArg Matrix.conjTranspose h1
  have h2a := congrArg Matrix.conjTranspose h2
  simp only [Matrix.conjTranspose_add,Matrix.conjTranspose_zero,
    traceSecond_adjoint,traceFirst_adjoint] at h1a h2a
  constructor
  · simpa only [vectorization_second] using h1a
  · simpa only [vectorization_first] using h2a

def schmidtMatrix (k : ℝ) (s t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ![![(k*s : ℝ),0],![0,(k*t : ℝ)]]

theorem offdiagonal_rows (k s t : ℝ) (hk : k≠0)
    (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (h : PartialTraceRows (schmidtMatrix k s t) A B) :
    ((s : ℂ)*star (B 1 0)+(t : ℂ)*A 0 1=0) ∧
    ((t : ℂ)*star (B 1 0)+(s : ℂ)*A 0 1=0) ∧
    ((t : ℂ)*star (B 0 1)+(s : ℂ)*A 1 0=0) ∧
    ((s : ℂ)*star (B 0 1)+(t : ℂ)*A 1 0=0) := by
  have h00 := congrFun (congrFun h.1 0) 1
  have h01 := congrFun (congrFun h.2 0) 1
  have h10 := congrFun (congrFun h.1 1) 0
  have h11 := congrFun (congrFun h.2 1) 0
  simp only [Matrix.add_apply,Matrix.mul_apply,Fin.sum_univ_two,
    Matrix.conjTranspose_apply,Matrix.transpose_apply,Matrix.map_apply,
    Matrix.zero_apply,schmidtMatrix,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,star_zero,mul_zero,zero_mul,add_zero,zero_add] at h00 h01 h10 h11
  simp only [Complex.star_def,Complex.conj_ofReal] at h00 h01 h10 h11
  norm_num at h00 h01 h10 h11
  have hkc : (k : ℂ)≠0 := by exact_mod_cast hk
  refine ⟨?_,?_,?_,?_⟩
  all_goals simp only [Complex.star_def]
  · apply mul_left_cancel₀ hkc
    linear_combination h00
  · apply mul_left_cancel₀ hkc
    linear_combination h11
  · apply mul_left_cancel₀ hkc
    linear_combination h10
  · apply mul_left_cancel₀ hkc
    linear_combination h01

theorem physical_schmidt_offdiagonal_rows (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (hvu : vv d=uu c)
    (k s t : ℝ) (hk : k≠0) (hU : coefficientMatrix (uu c)=schmidtMatrix k s t)
    (i : Fin 4) :
    ((s : ℂ)*star (coefficientMatrix (topVector d i) 1 0)+
      (t : ℂ)*coefficientMatrix (bottomVector c i) 0 1=0) ∧
    ((t : ℂ)*star (coefficientMatrix (topVector d i) 1 0)+
      (s : ℂ)*coefficientMatrix (bottomVector c i) 0 1=0) ∧
    ((t : ℂ)*star (coefficientMatrix (topVector d i) 0 1)+
      (s : ℂ)*coefficientMatrix (bottomVector c i) 1 0=0) ∧
    ((s : ℂ)*star (coefficientMatrix (topVector d i) 0 1)+
      (t : ℂ)*coefficientMatrix (bottomVector c i) 1 0=0) := by
  have h := physical_partial_trace_rows c d hc hd hnc hnd hkl hvu i
  rw [hU] at h
  exact offdiagonal_rows _ _ _ hk _ _ h

end
end MainTheory.Orbit5OffdiagonalDisplays
