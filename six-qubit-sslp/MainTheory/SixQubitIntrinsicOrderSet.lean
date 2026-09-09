import MainTheory.SixQubitIntrinsicAttainment
import MainTheory.IntrinsicOrderAudit

set_option autoImplicit false
namespace MainTheory.SixQubitIntrinsicOrderSet
open MainTheory.SixQubitIntrinsicAttainment
open MainTheory.GlobalClassificationBridge

theorem nontrivial_exact : attainedIntrinsicOrders=({2,3,5} : Set ℕ) := by
  apply Set.Subset.antisymm
  · rintro m ⟨C,g,hg,rfl⟩
    have hn : orderOf g ≠ 1 := by
      intro h
      exact hg (orderOf_eq_one_iff.mp h)
    rcases MainTheory.IntrinsicOrderAudit.orderOf_mem C g with h | h | h | h
    · exact False.elim (hn h)
    · simp [h]
    · simp [h]
    · simp [h]
  · exact two_three_five_subset_attained

theorem including_identity :
    {m : ℕ | ∃ C : MainTheory.CodeSpec.ExactCode 6 2 3,∃ g : IntrinsicGroup C,orderOf g=m}=
      ({1,2,3,5} : Set ℕ) := by
  ext m
  constructor
  · rintro ⟨C,g,rfl⟩
    rcases MainTheory.IntrinsicOrderAudit.orderOf_mem C g with h | h | h | h <;> simp [h]
  · intro h
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
    rcases h with rfl | h
    · obtain ⟨C,g,_⟩ := order_two_attained
      exact ⟨C,1,by simp⟩
    · have hm : m ∈ attainedIntrinsicOrders := by
        rw [nontrivial_exact]
        simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using h
      obtain ⟨C,g,_,hg⟩ := hm
      exact ⟨C,g,hg⟩
end MainTheory.SixQubitIntrinsicOrderSet
