import MainTheory.Orbit21WalshFace
import MainTheory.FullRankFlipObstruction

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace MainTheory.Orbit21FaceKL

open MainTheory.Orbit21MomentFace MainTheory.Orbit21WalshFace MainTheory.FlipCharacter

def S0 : Finset (SS.BitString 6) := Finset.univ.image bottom
def S1 : Finset (SS.BitString 6) := Finset.univ.image top
def dressing : Fin 7 → SS.BitString 6 := flipDressings (fun i : Fin 6 => i)

theorem top_injective : Function.Injective top := by decide +kernel
theorem incidences : Finset.univ.image top=incidenceSet S0 S1 (SS.stdBasis 3) := by decide +kernel
theorem matched_bottom : ∀ i,SS.bxor (top i) (SS.stdBasis 3)=bottom i := by decide +kernel

theorem dressing_weight (i : Fin 7) :
    (⟨SS.stdBasis 3,dressing i⟩ : SS.PauliString 6).wt ≤ 2 :=
  flipDressings_low_weight 3 (fun j : Fin 6 => j) i

theorem character_rows (i : Fin 7) (j : Fin 8) :
    character (dressing i) (top j)=(if i=4 then -1 else 1)*W i j := by
  change character (dressing i) (top j)=(if i=4 then -1 else 1)*(rows i j : ℂ)
  rw [← actual_rows]
  induction i using Fin.cases with
  | zero =>
    have hd : dressing 0=(fun _ => false) := rfl
    rw [hd,character_zero]
    fin_cases j <;> norm_num [walsh,Fin.ext_iff]
  | succ i =>
    have hd : dressing i.succ=SS.stdBasis i := rfl
    rw [hd,character_single]
    fin_cases i <;> fin_cases j <;>
      norm_num [top,bottom,walsh,MainTheory.Orbit21LiteralData.bits,SixQubit.Realize.nbit,Fin.rev,
        Nat.testBit,Nat.shiftRight_eq_div_pow,Fin.ext_iff]

theorem kernel_of_kl (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) :
    W.mulVec (fun i => star (c (bottom i))*d (top i))=0 := by
  funext i
  have h := SixQubit.offSumOn_eq_zero_of_hasDistance S0 S1 c d hc hd hkl
    (SS.stdBasis 3) (dressing i) (dressing_weight i)
  rw [offSum_eq_indexed S0 S1 c d (SS.stdBasis 3) (dressing i) top
    top_injective incidences] at h
  simp only [character_rows,incidenceMonomial,matched_bottom] at h
  simp_rw [mul_assoc] at h
  rw [← Finset.mul_sum] at h
  have hn : (if i=4 then (-1 : ℂ) else 1) ≠ 0 := by split_ifs <;> norm_num
  exact (mul_eq_zero.mp h).resolve_left hn

theorem uniform_of_kl (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (alpha beta : ℝ)
    (hm : ∀ i,‖star (c (bottom i))*d (top i)‖=pattern alpha beta i) :
    alpha=1/8 ∧ beta=1/8 :=
  uniform alpha beta _ (kernel_of_kl c d hc hd hkl) hm

theorem monomial_magnitude (c d : ℂ) (h : Complex.normSq c=Complex.normSq d) :
    ‖star c*d‖=Complex.normSq c := by
  rw [norm_mul,norm_star,Complex.norm_def,Complex.norm_def,← h,
    Real.mul_self_sqrt (Complex.normSq_nonneg c)]

theorem uniform_probabilities (c d : SS.State 6 ℂ)
    (hc : ∀ x,x ∉ S0 → c x=0) (hd : ∀ x,x ∉ S1 → d x=0)
    (hkl : SS.HasDistance ![c,d] 3) (p : Sum (Fin 8) (Fin 8) → ℝ)
    (hp : MainTheory.MomentPolytope.Feasible bottom top p)
    (hp0 : ∀ i,Complex.normSq (c (bottom i))=p (Sum.inl i))
    (hp1 : ∀ i,Complex.normSq (d (top i))=p (Sum.inr i)) :
    p (Sum.inl 0)=1/8 ∧ p (Sum.inl 2)=1/8 := by
  obtain ⟨h0,h1⟩ := probabilities p hp
  apply uniform_of_kl c d hc hd hkl
  intro i
  have he : Complex.normSq (c (bottom i))=Complex.normSq (d (top i)) := by
    rw [hp0,hp1,congrFun h0 i,congrFun h1 i]
  rw [monomial_magnitude _ _ he,hp0,congrFun h0 i]

end MainTheory.Orbit21FaceKL
