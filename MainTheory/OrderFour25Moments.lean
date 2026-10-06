import MainTheory.OrderFour25Support
import MainTheory.MomentPolytope
set_option autoImplicit false
set_option maxHeartbeats 16000000
namespace MainTheory.OrderFour25Moments
open MainTheory.OrderFour25Support MainTheory.MomentPolytope
open MainTheory.OrderEightSupportDisplays (bits)
noncomputable def total (t : Fin 5 → ℝ) (sigma : ℝ) : ℝ := t 0+t 1+t 2+t 3+t 4+sigma
noncomputable def bot (t : Fin 5 → ℝ) (sigma : ℝ) : Fin 12 → ℝ :=
  let T := total t sigma
  ![3/8-3*T/4+sigma,1/8-T/4+t 0,1/8-T/4+t 1,1/8-T/4+t 2,1/8-T/4+t 3,1/8-T/4+t 4,3*T/4-sigma,T/4-t 0,T/4-t 1,T/4-t 2,T/4-t 3,T/4-t 4]
noncomputable def up (t : Fin 5 → ℝ) (sigma : ℝ) : Fin 12 → ℝ := ![1/8-t 0,1/8-t 1,1/8-t 2,1/8-t 3,1/8-t 4,3/8-sigma,t 0,t 1,t 2,t 3,t 4,sigma]
noncomputable def parameters (p : Sum (Fin 12) (Fin 12) → ℝ) : Fin 5 → ℝ :=
  ![p (Sum.inr 6),p (Sum.inr 7),p (Sum.inr 8),p (Sum.inr 9),p (Sum.inr 10)]
theorem probabilities (p : Sum (Fin 12) (Fin 12) → ℝ)
    (H : Feasible bottom top p) :
    (fun i => p (Sum.inl i))=bot (parameters p) (p (Sum.inr 11)) ∧
    (fun i => p (Sum.inr i))=up (parameters p) (p (Sum.inr 11)) := by
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
  norm_num [mean0,mean1,second0,second1,coord,bottom,top,bits,
    Fin.sum_univ_succ,Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.succ] at hn0 hn1 hf0 hf1 hf2 hf3 hf4 hf5 h01 h02 h03 h04 h05 h12 h13 h14 h15 h23 h24 h25 h34 h35 h45
  constructor <;> funext i <;> fin_cases i <;>
    norm_num [bot,up,total,parameters,Fin.succ] <;> linarith!
end MainTheory.OrderFour25Moments
