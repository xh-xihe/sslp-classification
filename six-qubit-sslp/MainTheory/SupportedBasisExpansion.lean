import Mathlib
set_option autoImplicit false
namespace MainTheory.SupportedBasisExpansion
open scoped BigOperators

theorem supported_sum {α : Type*} [DecidableEq α] (S : Finset α) (c : α → ℂ)
    (hc : ∀ x,x∉S → c x=0) (x : α) :
    c x=∑ y ∈ S,if x=y then c y else 0 := by
  classical
  by_cases hx : x∈S
  · simp [hx]
  · simp [hx,hc x hx]

theorem indexed_sum {α β : Type*} [DecidableEq α] [Fintype β] [DecidableEq β]
    (f : β → α) (hf : Function.Injective f) (c : α → ℂ)
    (hc : ∀ x,x∉Finset.univ.image f → c x=0) (x : α) :
    c x=∑ i : β,if x=f i then c (f i) else 0 := by
  have h := supported_sum (Finset.univ.image f) c hc x
  rw [Finset.sum_image] at h
  · exact h
  · intro i _ j _ hij
    exact hf hij

end MainTheory.SupportedBasisExpansion
