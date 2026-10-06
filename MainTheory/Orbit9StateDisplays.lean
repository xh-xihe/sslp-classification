import MainTheory.Orbit9MomentDisplays

set_option autoImplicit false
set_option maxRecDepth 100000

namespace MainTheory.Orbit9StateDisplays

open SixQubit.Orbit9Universal

noncomputable def ket (y : SS.BitString 6) : SS.State 6 ℂ := fun x => if x=y then 1 else 0

theorem bottom_partition : ∀ x : SS.BitString 6,
    ((∑ i : Fin 6,if x=one i then 1 else 0)+
      ∑ ij ∈ pairIdx,if x=SS.complement (pair ij.1 ij.2) then 1 else 0 : ℕ)=
      if x ∈ S0 then 1 else 0 := by decide

theorem top_partition : ∀ x : SS.BitString 6,
    ((∑ i : Fin 6,if x=SS.complement (one i) then 1 else 0)+
      ∑ ij ∈ pairIdx,if x=pair ij.1 ij.2 then 1 else 0 : ℕ)=
      if x ∈ S1 then 1 else 0 := by decide

theorem bottom_expansion (c : SS.State 6 ℂ) (hc : ∀ x,x ∉ S0 → c x=0) :
    c=fun x => (∑ i,xamp c i*ket (one i) x)+
      ∑ ij ∈ pairIdx,damp c ij.1 ij.2*ket (SS.complement (pair ij.1 ij.2)) x := by
  funext x
  have hp : ((∑ i : Fin 6,if x=one i then (1 : ℂ) else 0)+
      ∑ ij ∈ pairIdx,if x=SS.complement (pair ij.1 ij.2) then (1 : ℂ) else 0)=
      if x ∈ S0 then (1 : ℂ) else 0 := by exact_mod_cast bottom_partition x
  have he := congrArg (fun z : ℂ => z*c x) hp
  simp only [add_mul,Finset.sum_mul,ite_mul,one_mul,zero_mul] at he
  have hval : (if x ∈ S0 then c x else 0)=c x := by
    by_cases hx : x ∈ S0 <;> simp [hx,hc x]
  rw [hval] at he
  rw [← he]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp only [xamp,ket,mul_ite,mul_one,mul_zero]
    split_ifs with h <;> simp_all
  · apply Finset.sum_congr rfl
    intro ij hij
    have hn := ne_of_lt (Finset.mem_filter.mp hij).2
    simp only [damp,if_neg hn,ket,mul_ite,mul_one,mul_zero]
    split_ifs with h <;> simp_all

theorem top_expansion (d : SS.State 6 ℂ) (hd : ∀ x,x ∉ S1 → d x=0) :
    d=fun x => (∑ ij ∈ pairIdx,camp d ij.1 ij.2*ket (pair ij.1 ij.2) x)+
      ∑ i,yamp d i*ket (SS.complement (one i)) x := by
  funext x
  have hp : ((∑ i : Fin 6,if x=SS.complement (one i) then (1 : ℂ) else 0)+
      ∑ ij ∈ pairIdx,if x=pair ij.1 ij.2 then (1 : ℂ) else 0)=
      if x ∈ S1 then (1 : ℂ) else 0 := by exact_mod_cast top_partition x
  have he := congrArg (fun z : ℂ => z*d x) hp
  simp only [add_mul,Finset.sum_mul,ite_mul,one_mul,zero_mul] at he
  have hval : (if x ∈ S1 then d x else 0)=d x := by
    by_cases hx : x ∈ S1 <;> simp [hx,hd x]
  rw [hval] at he
  rw [← he,add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro ij hij
    have hn := ne_of_lt (Finset.mem_filter.mp hij).2
    simp only [camp,if_neg hn,ket,mul_ite,mul_one,mul_zero]
    split_ifs with h <;> simp_all
  · apply Finset.sum_congr rfl
    intro i _
    simp only [yamp,ket,mul_ite,mul_one,mul_zero]
    split_ifs with h <;> simp_all

end MainTheory.Orbit9StateDisplays
