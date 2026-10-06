import MainTheory.OrderSevenSupportDisplays
import MainTheory.MomentPolytope

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace MainTheory.OrderSevenMoment58
open MainTheory.OrderSevenSupportDisplays MainTheory.MomentPolytope
open MainTheory.OrderEightSupportDisplays (bits)

noncomputable def pattern (s t : ℝ) : Fin 9 → ℝ := ![t,1/14,1/14,s,5/14-s-t,1/7,2/7-t,3/14-s,s+t-1/7]

theorem probabilities (p : Sum (Fin 9) (Fin 9) → ℝ)
    (H : Feasible bottom58 top58 p) :
    (fun i => p (Sum.inl i))=pattern (p (Sum.inl 3)) (p (Sum.inl 0)) ∧ (fun i => p (Sum.inr i))=pattern (p (Sum.inl 3)) (p (Sum.inl 0)) := by
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
  norm_num [mean0,mean1,second0,second1,coord,bottom58,top58,bits,SS.complement,
    Fin.sum_univ_succ,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ] at hn0 hn1 hf0 hf1 hf2 hf3 hf4 hf5 h01 h02 h03 h04 h05 h12 h13 h14 h15 h23 h24 h25 h34 h35 h45
  constructor <;> funext i <;> fin_cases i <;> norm_num [pattern,Fin.succ] <;> linarith!

theorem equal_probabilities (p : Sum (Fin 9) (Fin 9) → ℝ)
    (H : Feasible bottom58 top58 p) : ∀ i,p (Sum.inl i)=p (Sum.inr i) := by
  intro i
  exact congrFun ((probabilities p H).1.trans (probabilities p H).2.symm) i

end MainTheory.OrderSevenMoment58
