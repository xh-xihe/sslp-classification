import MainTheory.Orbit21IntrinsicRealization
import MainTheory.Orbit9IntrinsicRealization
import MainTheory.WImageIntrinsicBridge

/-!
# Attained intrinsic orders on exact six-qubit codes

This lightweight endpoint only aggregates three independently constructed
positive examples.  It states that orders two, three, and five are each
attained by an element of the actual intrinsic projective diagonal group of
some exact `((6,2,3))` code.  The three existential codes are allowed to be
different.

No converse is asserted: this file does not exclude any other order, does not
construct a bounded cover or an order audit, and does not identify the order
of the whole intrinsic group of any witness code.
-/

namespace MainTheory.SixQubitIntrinsicAttainment

open MainTheory
open MainTheory.GlobalClassificationBridge

/-- An intrinsic element order is attained when some genuine exact
six-qubit code has a nonidentity quotient element of exactly that
group-theoretic order. -/
def AttainedIntrinsicOrder (m : ℕ) : Prop :=
  ∃ C : CodeSpec.ExactCode 6 2 3,
    ∃ g : IntrinsicGroup C, g ≠ 1 ∧ orderOf g = m

/-- The set of group-theoretic element orders attained by the certified
positive examples, defined semantically rather than from paper labels. -/
def attainedIntrinsicOrders : Set ℕ :=
  {m | AttainedIntrinsicOrder m}

@[simp] theorem mem_attainedIntrinsicOrders_iff (m : ℕ) :
    m ∈ attainedIntrinsicOrders ↔ AttainedIntrinsicOrder m := by
  rfl

theorem order_two_attained : AttainedIntrinsicOrder 2 :=
  MainTheory.Orbit21IntrinsicRealization.exists_exact_six_qubit_intrinsic_order_two

theorem order_three_attained : AttainedIntrinsicOrder 3 :=
  MainTheory.Orbit9IntrinsicRealization.exists_exact_six_qubit_intrinsic_order_three

theorem order_five_attained : AttainedIntrinsicOrder 5 :=
  MainTheory.WImageIntrinsicBridge.exists_exact_six_qubit_intrinsic_order_five

/-- Conjunction form of the three independent positive realization results. -/
theorem two_three_five_attained :
    AttainedIntrinsicOrder 2 ∧
      AttainedIntrinsicOrder 3 ∧ AttainedIntrinsicOrder 5 :=
  ⟨order_two_attained, order_three_attained, order_five_attained⟩

/-- Set-theoretic lower bound on the attained-order set.  This is an
inclusion, deliberately not an equality. -/
theorem two_three_five_subset_attained :
    ({2, 3, 5} : Set ℕ) ⊆ attainedIntrinsicOrders := by
  intro m hm
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  rcases hm with h2 | h3 | h5
  · subst m
    exact order_two_attained
  · subst m
    exact order_three_attained
  · subst m
    exact order_five_attained

end MainTheory.SixQubitIntrinsicAttainment
