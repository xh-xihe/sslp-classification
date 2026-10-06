import MainTheory.QMinBound

/-!
# `thm:finite-projective-group`, in one statement

Section II's Theorem 2.5 has three clauses:

> the projective diagonal logical group is finite abelian; every projective
> element has a primitive finite root-of-unity physical lift; and for a
> nontrivial element, if `m` is its projective logical order and `q` the order
> of any finite physical lift, then `m | q`.

They were proved here as three separate results in three modules --
`GeneralFiniteness.finite_and_abelian`, `GeneralLiftOrder.exists_hasPrimitiveLift`
and `orderOf_dvd_of_hasPrimitiveLift` -- so a reader looking for the theorem
under one name would find only its first clause.  That is the same defect an
independent audit found in `thm:rank-two-sslp`, and later in
`thm:qualitative-finite-lift`; this is the last of the three.

The split by generality is the paper's own, in the sense that only finiteness
needs more than `Z_j` detection: the lift clauses hold at arbitrary rank, while
finiteness is available here only at `K = 2` and `d = 3`, because the route to
it runs on the distance-three rationalization rather than on the paper's
compact-Lie-group argument.
-/

namespace MainTheory.FiniteProjectiveGroup

open MainTheory
open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.GeneralLiftOrder

variable {n K d : ℕ}

/-- **The lift clauses of `thm:finite-projective-group`, at arbitrary rank.**

Every projective diagonal class has a primitive finite root-of-unity lift, and
its order divides the modulus of *any* such lift.  Neither clause needs
finiteness of the group; both need only `Z_j` detection. -/
theorem lifts (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d) :
    (∀ g : IntrinsicGroup C, ∃ q : ℕ, 0 < q ∧ HasPrimitiveLift C g q) ∧
    (∀ (g : IntrinsicGroup C) (q : ℕ), HasPrimitiveLift C g q →
      orderOf g ∣ q) ∧
    (∀ g : IntrinsicGroup C, 0 < orderOf g) :=
  ⟨fun g => exists_hasPrimitiveLift C hd g,
    fun _ _ h => orderOf_dvd_of_hasPrimitiveLift h,
    fun g => orderOf_pos C hd g⟩

/-- **`thm:finite-projective-group`, conditionally on finiteness.**

At arbitrary rank the group is abelian and the lift clauses hold; finiteness is
taken as a hypothesis, which is exactly where the paper appeals to its
compact-Lie-group argument. -/
theorem whole_of_finite (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d)
    (hfin : Finite (IntrinsicGroup C)) :
    Finite (IntrinsicGroup C) ∧
    (∀ g h : IntrinsicGroup C, g * h = h * g) ∧
    (∀ g : IntrinsicGroup C, ∃ q : ℕ, 0 < q ∧ HasPrimitiveLift C g q) ∧
    (∀ (g : IntrinsicGroup C) (q : ℕ), HasPrimitiveLift C g q →
      orderOf g ∣ q) := by
  obtain ⟨hex, hdvd, _⟩ := lifts C hd
  exact ⟨hfin, IntrinsicAbelian.intrinsicGroup_mul_comm _, hex, hdvd⟩

/-- **`thm:finite-projective-group`, unconditionally at `K = 2`, `d = 3`.**

All three clauses under one name, with no hypothesis: the group is finite and
abelian, every class has a primitive finite lift, and every class's order
divides every such lift's modulus. -/
theorem whole (C : CodeSpec.ExactCode n 2 3) :
    Finite (IntrinsicGroup C) ∧
    (∀ g h : IntrinsicGroup C, g * h = h * g) ∧
    (∀ g : IntrinsicGroup C, ∃ q : ℕ, 0 < q ∧ HasPrimitiveLift C g q) ∧
    (∀ (g : IntrinsicGroup C) (q : ℕ), HasPrimitiveLift C g q →
      orderOf g ∣ q) :=
  whole_of_finite C GeneralFiniteness.two_le_three
    (GeneralFiniteness.finite_intrinsicGroup C)

/-- The six-qubit instance, with the certified modulus bound attached: the
group is finite abelian, and every class has a primitive lift of modulus at
most nine. -/
theorem whole_six_qubit (C : CodeSpec.ExactCode 6 2 3) :
    Finite (IntrinsicGroup C) ∧
    (∀ g h : IntrinsicGroup C, g * h = h * g) ∧
    (∀ g : IntrinsicGroup C, ∃ q : ℕ, 0 < q ∧ q ≤ 9 ∧
      HasPrimitiveLift C g q ∧ orderOf g ∣ q) := by
  obtain ⟨hfin, hcomm, _, _⟩ := whole C
  refine ⟨hfin, hcomm, fun g => ?_⟩
  obtain ⟨q, hqpos, hqB, hlift, hdvd⟩ := QMinBound.d3_bound_nine C g
  exact ⟨q, hqpos, hqB, hlift, hdvd⟩

end MainTheory.FiniteProjectiveGroup
