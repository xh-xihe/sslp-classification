import MainTheory.MomentPolytope
import MainTheory.Orbit21LiteralData

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace MainTheory.Orbit21MomentFace

open MainTheory.MomentPolytope MainTheory.Orbit21LiteralData

def bottom : Fin 8 → SS.BitString 6 := fun i => bits (![0,9,23,28,39,44,50,59] i)
def top : Fin 8 → SS.BitString 6 := fun i => bits (![4,13,19,24,35,40,54,63] i)

noncomputable def pattern (alpha beta : ℝ) : Fin 8 → ℝ :=
  ![alpha,1/4-alpha,beta,1/4-beta,1/4-beta,beta,1/4-alpha,alpha]

theorem matched_top : ∀ i : Fin 8,top i=SS.bxor (bottom i) (SS.stdBasis 3) := by decide +kernel

theorem probabilities (p : Sum (Fin 8) (Fin 8) → ℝ) (H : Feasible bottom top p) :
    (fun i => p (Sum.inl i))=pattern (p (Sum.inl 0)) (p (Sum.inl 2)) ∧
    (fun i => p (Sum.inr i))=pattern (p (Sum.inl 0)) (p (Sum.inl 2)) := by
  have hn0 := H.norm0
  have hn1 := H.norm1
  have hf0 := H.firstMoment 0
  have hf1 := H.firstMoment 1
  have hf2 := H.firstMoment 2
  have hf3 := H.firstMoment 3
  have hf4 := H.firstMoment 4
  have hf5 := H.firstMoment 5
  have h01 := H.secondMoment ⟨(0,1),by decide⟩
  have h02 := H.secondMoment ⟨(0,2),by decide⟩
  have h03 := H.secondMoment ⟨(0,3),by decide⟩
  have h04 := H.secondMoment ⟨(0,4),by decide⟩
  have h05 := H.secondMoment ⟨(0,5),by decide⟩
  have h12 := H.secondMoment ⟨(1,2),by decide⟩
  have h13 := H.secondMoment ⟨(1,3),by decide⟩
  have h14 := H.secondMoment ⟨(1,4),by decide⟩
  have h15 := H.secondMoment ⟨(1,5),by decide⟩
  have h23 := H.secondMoment ⟨(2,3),by decide⟩
  have h24 := H.secondMoment ⟨(2,4),by decide⟩
  have h25 := H.secondMoment ⟨(2,5),by decide⟩
  have h34 := H.secondMoment ⟨(3,4),by decide⟩
  have h35 := H.secondMoment ⟨(3,5),by decide⟩
  have h45 := H.secondMoment ⟨(4,5),by decide⟩
  norm_num [mean0,mean1,second0,second1,coord,bottom,top,bits,SixQubit.Realize.nbit,
    Fin.sum_univ_succ,Fin.rev,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ] at hn0 hn1 hf0 hf1 hf2 hf3 hf4 hf5 h01 h02 h03 h04 h05 h12 h13 h14 h15 h23 h24 h25 h34 h35 h45
  constructor <;> funext i <;> fin_cases i <;> norm_num [pattern,Fin.succ] <;> linarith!

theorem parameter_bounds (p : Sum (Fin 8) (Fin 8) → ℝ) (H : Feasible bottom top p) :
    0 ≤ p (Sum.inl 0) ∧ p (Sum.inl 0) ≤ 1/4 ∧
    0 ≤ p (Sum.inl 2) ∧ p (Sum.inl 2) ≤ 1/4 := by
  have h1 := congrFun (probabilities p H).1 1
  have h3 := congrFun (probabilities p H).1 3
  change p (Sum.inl 1)=1/4-p (Sum.inl 0) at h1
  change p (Sum.inl 3)=1/4-p (Sum.inl 2) at h3
  have hn1 := H.nonneg (Sum.inl 1)
  have hn3 := H.nonneg (Sum.inl 3)
  exact ⟨H.nonneg (Sum.inl 0),by linarith,H.nonneg (Sum.inl 2),by linarith⟩

end MainTheory.Orbit21MomentFace
