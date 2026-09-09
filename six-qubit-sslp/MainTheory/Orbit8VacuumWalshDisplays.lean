import SixQubit.Orbit8UniversalStar

set_option autoImplicit false

namespace MainTheory.Orbit8VacuumWalshDisplays

open SixQubit SixQubit.Orbit8Universal

noncomputable def m0 (c d : SS.State 6 ℂ) (i : Fin 6) : ℂ := star (c zero6)*u d i
noncomputable def mR (c d : SS.State 6 ℂ) (i : Fin 6) (ij : Fin 6 × Fin 6) : ℂ :=
  star (c (topRecip i ij))*v d ij.1 ij.2

theorem reciprocal_word : ∀ i : Fin 6, ∀ ij ∈ awayPairs i,
    topRecip i ij=SS.complement (tripleMask ij.1 ij.2 i) := by decide

theorem reciprocal_count : ∀ i : Fin 6,(awayPairs i).card=10 := by decide

theorem total_equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,SS.weight av x ≠ 0 → c x=0)
    (hd : ∀ x,SS.weight av x ≠ 1 → d x=0)
    (hcode : SS.HasDistance ![c,d] 3) (i : Fin 6) :
    m0 c d i+∑ ij ∈ awayPairs i,mR c d i ij=0 := by
  have h := offSumOn_eq_zero_of_hasDistance S0 S1 c d (full_support0 hc)
    (full_support1 hd) hcode (SS.stdBasis i) zero6 (wt_singleton_zero i)
  simpa only [offSum_single_expand,bdot_zero6,signMul_false,m0,mR] using h

theorem omitted_equation (c d : SS.State 6 ℂ)
    (hc : ∀ x,SS.weight av x ≠ 0 → c x=0)
    (hd : ∀ x,SS.weight av x ≠ 1 → d x=0)
    (hcode : SS.HasDistance ![c,d] 3) (i j : Fin 6) (hij : i ≠ j) :
    (∑ ij ∈ awayPairs i,if touches ij j = true then 0 else mR c d i ij)=0 := by
  have h0 := total_equation c d hc hd hcode i
  have hv : m0 c d i=0 := vacuum_singleton_product c d hc hd hcode i
  rw [hv,zero_add] at h0
  have ht := congrArg star (star_equation c d hc hd hcode i j hij)
  have ht' : (∑ ij ∈ awayPairs i,if touches ij j=true then mR c d i ij else 0)=0 := by
    simpa [mR,star_sum,apply_ite,mul_comm] using ht
  have hp : (∑ ij ∈ awayPairs i,if touches ij j=true then 0 else mR c d i ij)=
      (∑ ij ∈ awayPairs i,mR c d i ij)-
        (∑ ij ∈ awayPairs i,if touches ij j=true then mR c d i ij else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ij _
    split_ifs <;> simp
  rw [hp,h0,ht',sub_self]

end MainTheory.Orbit8VacuumWalshDisplays
