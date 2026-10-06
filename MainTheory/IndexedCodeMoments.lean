import MainTheory.MomentPolytope
import SixQubit.CodeBridge

/-! Actual supported code amplitudes supply every indexed degree-two moment
constraint. The fibers may have different sizes and may contain zero entries. -/
set_option autoImplicit false
namespace MainTheory.IndexedCodeMoments
open scoped BigOperators
noncomputable section
variable {N M : ℕ}

theorem sum_indexed (S : Finset (SS.BitString 6)) (xs : Fin N → SS.BitString 6)
    (hi : Function.Injective xs) (hs : Finset.univ.image xs=S)
    (f : SS.BitString 6 → ℝ) : (∑ i, f (xs i))=∑ x ∈ S, f x := by
  rw [← hs,Finset.sum_image hi.injOn]

theorem first_indexed (S : Finset (SS.BitString 6)) (xs : Fin N → SS.BitString 6)
    (hi : Function.Injective xs) (hs : Finset.univ.image xs=S)
    (c : SS.State 6 ℂ) (j : Fin 6) :
    (∑ i, Complex.normSq (c (xs i))*MomentPolytope.coord (xs i) j)=
      SixQubit.occOn S c j := by
  rw [sum_indexed S xs hi hs (fun x => Complex.normSq (c x)*MomentPolytope.coord x j)]
  unfold SixQubit.occOn
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  cases hx : x j <;> simp [MomentPolytope.coord,hx]

theorem second_indexed (S : Finset (SS.BitString 6)) (xs : Fin N → SS.BitString 6)
    (hi : Function.Injective xs) (hs : Finset.univ.image xs=S)
    (c : SS.State 6 ℂ) (j k : Fin 6) :
    (∑ i, Complex.normSq (c (xs i))*MomentPolytope.coord (xs i) j*
      MomentPolytope.coord (xs i) k)=SixQubit.occ2On S c j k := by
  rw [sum_indexed S xs hi hs (fun x => Complex.normSq (c x)*MomentPolytope.coord x j*
    MomentPolytope.coord x k)]
  unfold SixQubit.occ2On
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  cases hj : x j <;> cases hk : x k <;> simp [MomentPolytope.coord,hj,hk]

def probabilities (xs : Fin N → SS.BitString 6) (ys : Fin M → SS.BitString 6)
    (c d : SS.State 6 ℂ) : Sum (Fin N) (Fin M) → ℝ
  | .inl i => Complex.normSq (c (xs i))
  | .inr i => Complex.normSq (d (ys i))

theorem physical_feasible (S0 S1 : Finset (SS.BitString 6))
    (xs : Fin N → SS.BitString 6) (ys : Fin M → SS.BitString 6)
    (hxi : Function.Injective xs) (hyi : Function.Injective ys)
    (hxs : Finset.univ.image xs=S0) (hys : Finset.univ.image ys=S1)
    (c d : SS.State 6 ℂ) (hc : ∀ x, x ∉ S0 → c x=0)
    (hd : ∀ x, x ∉ S1 → d x=0)
    (hnc : SS.innerC c c=1) (hnd : SS.innerC d d=1)
    (hkl : SS.HasDistance ![c,d] 3) :
    MomentPolytope.Feasible xs ys (probabilities xs ys c d) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · rintro (i | i) <;> exact Complex.normSq_nonneg _
  · change (∑ i, Complex.normSq (c (xs i)))=1
    rw [sum_indexed S0 xs hxi hxs (fun x => Complex.normSq (c x))]
    exact SixQubit.massOn_eq_one S0 c hc hnc
  · change (∑ i, Complex.normSq (d (ys i)))=1
    rw [sum_indexed S1 ys hyi hys (fun x => Complex.normSq (d x))]
    exact SixQubit.massOn_eq_one S1 d hd hnd
  · intro j
    change (∑ i, Complex.normSq (c (xs i))*MomentPolytope.coord (xs i) j)=
      ∑ i, Complex.normSq (d (ys i))*MomentPolytope.coord (ys i) j
    rw [first_indexed S0 xs hxi hxs,first_indexed S1 ys hyi hys]
    exact SixQubit.occOn_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hkl j
  · intro jk
    change (∑ i, Complex.normSq (c (xs i))*MomentPolytope.coord (xs i) jk.1.1*
      MomentPolytope.coord (xs i) jk.1.2)=
      ∑ i, Complex.normSq (d (ys i))*MomentPolytope.coord (ys i) jk.1.1*
        MomentPolytope.coord (ys i) jk.1.2
    rw [second_indexed S0 xs hxi hxs,second_indexed S1 ys hyi hys]
    exact SixQubit.occ2On_eq_of_hasDistance S0 S1 c d hc hd hnc hnd hkl _ _
end
end MainTheory.IndexedCodeMoments
