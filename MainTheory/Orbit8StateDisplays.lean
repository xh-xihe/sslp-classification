import MainTheory.Orbit8PhaseNormalization
import MainTheory.Orbit8SpinSemantics
import SixQubit.Orbit8UniversalMagnitudes

set_option autoImplicit false

namespace MainTheory.Orbit8StateDisplays

open SixQubit.Orbit8Universal MainTheory.Orbit8SpinSemantics

theorem bottom_cases : ∀ x : SS.BitString 6,
    (SS.hammingWt x=0 → x=zero6) ∧
    (SS.hammingWt x=6 → x=ones6) ∧
    (SS.hammingWt x=3 → x ∈ S0) := by decide

theorem bottom_expansion (c : SS.State 6 ℂ)
    (hc : ∀ x,SS.weight av x ≠ 0 → c x=0) (hzero : c zero6=0) :
    c = fun x => ball c*ket ones6 x +
      ∑ y ∈ Finset.univ.filter (fun y : SS.BitString 6 => SS.hammingWt y=3),
        c y*ket y x := by
  classical
  funext x
  simp only [ket,mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_eq,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hx : x ∈ S0
  · rcases S0_shells x hx with h | h | h
    · have he := (bottom_cases x).1 h
      subst x
      simp [hzero,h,show zero6 ≠ ones6 by decide]
    · have hn : x ≠ ones6 := by
        intro he
        subst x
        norm_num [ones6,SS.hammingWt] at h
      simp [h,hn]
    · have he := (bottom_cases x).2.1 h
      subst x
      simp [ball,ones6,SS.hammingWt]
  · have hz := full_support0 hc x hx
    have h3 : SS.hammingWt x ≠ 3 := fun h => hx ((bottom_cases x).2.2 h)
    have hn : x ≠ ones6 := by
      intro he
      subst x
      exact hx (by decide)
    simp [hz,h3,hn]

theorem top_partition : ∀ x : SS.BitString 6,
    ((∑ i : Fin 6,if x=SS.stdBasis i then 1 else 0)+
      ∑ ij ∈ pairs6,if x=SS.complement (pairMask ij.1 ij.2) then 1 else 0 : ℕ)=
      if x ∈ S1 then 1 else 0 := by decide

theorem top_expansion (d : SS.State 6 ℂ)
    (hd : ∀ x,SS.weight av x ≠ 1 → d x=0) :
    d = fun x => (∑ i : Fin 6,u d i*ket (SS.stdBasis i) x)+
      ∑ ij ∈ pairs6,v d ij.1 ij.2*ket (SS.complement (pairMask ij.1 ij.2)) x := by
  funext x
  have hp : ((∑ i : Fin 6,if x=SS.stdBasis i then (1 : ℂ) else 0)+
      ∑ ij ∈ pairs6,if x=SS.complement (pairMask ij.1 ij.2) then (1 : ℂ) else 0)=
      if x ∈ S1 then (1 : ℂ) else 0 := by exact_mod_cast top_partition x
  have he := congrArg (fun z : ℂ => z*d x) hp
  simp only [add_mul,Finset.sum_mul,ite_mul,one_mul,zero_mul] at he
  simp only [u,v,ket,mul_ite,mul_one,mul_zero]
  have hval : (if x ∈ S1 then d x else 0)=d x := by
    by_cases hx : x ∈ S1
    · simp [hx]
    · simp [hx,full_support1 hd x hx]
  rw [hval] at he
  rw [← he]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    split_ifs with h <;> simp_all
  · apply Finset.sum_congr rfl
    intro ij _
    split_ifs with h <;> simp_all

end MainTheory.Orbit8StateDisplays
