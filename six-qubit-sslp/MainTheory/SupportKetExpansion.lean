import SixQubit.Common
import SS.DiagonalAction

set_option autoImplicit false

namespace MainTheory.SupportKetExpansion

def ket {n : ℕ} (x : SS.BitString n) : SS.State n ℂ := fun y => if y=x then 1 else 0

theorem expansion {n : ℕ} (S : Finset (SS.BitString n)) (c : SS.State n ℂ)
    (hc : ∀ x,x ∉ S → c x=0) : c=∑ x ∈ S,c x • ket x := by
  classical
  ext y
  by_cases hy : y ∈ S
  · simp [ket,Finset.sum_apply,hy,Pi.smul_apply]
  · simp [ket,Finset.sum_apply,hy,Pi.smul_apply,hc y hy]

theorem indexed_expansion {n k : ℕ} (S : Finset (SS.BitString n))
    (xs : Fin k → SS.BitString n) (hi : Function.Injective xs)
    (hs : Finset.univ.image xs=S) (c : SS.State n ℂ) (hc : ∀ x,x ∉ S → c x=0) :
    c=∑ i,c (xs i) • ket (xs i) := by
  calc
    c=∑ x ∈ S,c x • ket x := expansion S c hc
    _=∑ i,c (xs i) • ket (xs i) := by rw [← hs,Finset.sum_image hi.injOn]

end MainTheory.SupportKetExpansion
