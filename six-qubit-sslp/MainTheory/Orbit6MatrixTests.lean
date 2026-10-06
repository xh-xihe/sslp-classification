import MainTheory.Orbit6SpinorDisplays
set_option autoImplicit false
namespace MainTheory.Orbit6MatrixTests
open scoped Matrix BigOperators
open SixQubit.Orbit6 MainTheory.Orbit6MomentDisplays MainTheory.Orbit6SpinorDisplays
noncomputable section

theorem trace_outer (F : Matrix (Fin 2) (Fin 2) ℂ) (u v : Fin 2 → ℂ) :
    Matrix.trace (F*Matrix.vecMulVec v (star u))=pairing u (F.mulVec v) := by
  simp only [Matrix.trace,Matrix.diag,Fin.sum_univ_two,Matrix.mul_apply,
    Matrix.vecMulVec_apply,Matrix.mulVec,dotProduct,Pi.star_apply,pairing]
  ring

def incidentTest (F : Matrix (Fin 2) (Fin 2) ℂ)
    (c d : SS.State 6 ℂ) (k : Fin 5) : ℂ :=
  ∑ e : Fin 10,if k=(edges e).1 then
    pairing (bottomEdge c e) (F.mulVec (topComplement d (edges e).2))
  else if k=(edges e).2 then
    pairing (bottomEdge c e) (F.mulVec (topComplement d (edges e).1)) else 0

theorem trace_edge_test (F : Matrix (Fin 2) (Fin 2) ℂ)
    (c d : SS.State 6 ℂ) (k : Fin 5) :
    Matrix.trace (F*edgeOuter c d k)=incidentTest F c d k := by
  classical
  unfold edgeOuter incidentTest
  rw [Matrix.mul_sum,Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp only [trace_outer,Matrix.mul_zero,Matrix.trace_zero]

theorem physical_matrix_tests (c d : SS.State 6 ℂ)
    (hc : ∀ x,x∉S0 → c x=0) (hd : ∀ x,x∉S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) (k : Fin 5)
    (F : Matrix (Fin 2) (Fin 2) ℂ) :
    pairing (anchor c) (F.mulVec (topSingleton d k))+incidentTest F c d k=0 := by
  have h : Matrix.trace (F*(Matrix.vecMulVec (topSingleton d k) (star (anchor c))+
      edgeOuter c d k))=0 := by
    rw [physical_matrix_identity c d hc hd hnc hnd hkl k,Matrix.mul_zero,Matrix.trace_zero]
  rw [Matrix.mul_add,Matrix.trace_add,trace_outer,trace_edge_test] at h
  exact h

end
end MainTheory.Orbit6MatrixTests
