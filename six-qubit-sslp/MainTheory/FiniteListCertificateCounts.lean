import Mathlib

/-! Relate a linear list check to indexed finite-domain semantics. -/
set_option autoImplicit false

namespace MainTheory.FiniteListCertificateCounts
open scoped BigOperators

theorem sum_indicator_eq_filter_length {α : Type*} (l : List α) (f : α → Bool) :
    (∑ j : Fin l.length, if f l[j.val] = true then (1 : ℕ) else 0) =
      (l.filter f).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons]
    rw [Fin.sum_univ_succ]
    simpa only [List.length_cons,List.getElem_cons_zero,List.getElem_cons_succ,
      List.filter_cons,List.length_cons,Fin.val_zero,Fin.val_succ] using
      (show (if f a = true then 1 else 0) +
        (∑ j : Fin l.length, if f l[j.val] = true then (1 : ℕ) else 0) =
        (List.filter f (a::l)).length by rw [ih]; cases h : f a <;> simp [h,Nat.add_comm])

theorem indexed_filter_card {α : Type*} (l : List α) (f : α → Bool) :
    (Finset.univ.filter fun j : Fin l.length => f l[j.val] = true).card =
      (l.filter f).length := by
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  exact sum_indicator_eq_filter_length l f

end MainTheory.FiniteListCertificateCounts
