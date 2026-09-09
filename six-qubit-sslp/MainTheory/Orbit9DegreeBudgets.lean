import SixQubit.Orbit9SupportCard

set_option autoImplicit false

namespace MainTheory.Orbit9DegreeBudgets

open SixQubit.Orbit9Universal

theorem inactive_budget (c d : SS.State 6 ℂ) (H : FullKL c d) :
    (∑ i ∈ Finset.univ \ ActiveSet c,Rdeg c i)=(6-((ActiveSet c).card : ℝ))/6 := by
  classical
  have he (i : Fin 6) (hi : i ∈ Finset.univ \ ActiveSet c) : Rdeg c i=(1/6 : ℝ) := by
    have hn : ¬ Active c i := fun h => (Finset.mem_sdiff.mp hi).2 ((mem_ActiveSet c i).mpr h)
    rw [(pq_degree c d H.support0 H.support1 H.norm0 H.norm1 H.distance i).2.1,
      p_eq_zero_of_not_active c i hn,add_zero]
  rw [Finset.sum_congr rfl he,Finset.sum_const,Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  have hn : (ActiveSet c).card ≤ (Finset.univ : Finset (Fin 6)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [nsmul_eq_mul,Nat.cast_sub hn]
  norm_num
  ring

theorem degree_budgets (c d : SS.State 6 ℂ) (H : FullKL c d) :
    (∑ i ∈ ActiveSet c,Rdeg c i)=((ActiveSet c).card : ℝ)/6+1/3 ∧
    (∑ i ∈ Finset.univ \ ActiveSet c,Rdeg c i)=(6-((ActiveSet c).card : ℝ))/6 :=
  ⟨active_degree_sum c d H,inactive_budget c d H⟩

end MainTheory.Orbit9DegreeBudgets
