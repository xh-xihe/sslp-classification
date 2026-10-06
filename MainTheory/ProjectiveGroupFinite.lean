import Mathlib
import MainTheory.Cyclic

/-!
# Finite projective diagonal groups from a bounded lift cover

This module records the elementary, kernel-checkable route from the *uniform*
finite-lift theorem to finiteness of the projective logical group.

It is important not to confuse this route with the earlier structural argument
in `documents/20260822/main.tex`, Theorem `thm:finite-projective-group`.  The
paper proves finiteness before any denominator bound, using the facts that the
physical stabilizer is a closed subgroup of a compact torus and that its
projective logical image has zero Lie algebra.  The required compact-Lie-group
bridge is not presently formalized in this repository.

What is proved here is the strongest elementary replacement needed by the
later bounded classification:

* a lift with `1 <= q <= B` is encoded by a genuinely finite type of residue
  labels;
* if **every** projective action is represented by one of those labels, the
  action type is finite;
* a faithful phase-ratio character then makes a rank-two projective group
  cyclic;
* for any restriction homomorphism, logical order divides physical order.

The coverage obligation is deliberately a named structure field.  Merely
knowing that each selected gate has some finite lift, with no common bound,
does not instantiate `BoundedLiftCover` and is not used as if it did.
-/

namespace MainTheory.ProjectiveGroupFinite

open MainTheory

/-- A physical root-of-unity label with a modulus in `1, ..., B`.

The element `q : Fin B` represents the positive modulus `q.val + 1`; every
coordinate is stored exactly in the corresponding residue ring.  For `B = 0`
the type is empty, as it should be. -/
abbrev BoundedPhaseLabel (n B : ℕ) :=
  Σ q : Fin B, Fin n → ZMod (q.val + 1)

/-- An explicit statement that the bounded physical labels cover *all*
projective logical actions under consideration.

`actionOf` is allowed to forget redundant presentations: distinct moduli or
angle vectors may induce the same projective action.  Only surjectivity is
needed.  This is the global completeness obligation that must eventually be
discharged from the code-preserving gate semantics and the uniform lift bound.
-/
structure BoundedLiftCover (n B : ℕ) (G : Type*) where
  actionOf : BoundedPhaseLabel n B → G
  covers : Function.Surjective actionOf

/-- A bounded lift cover makes the entire projective action type finite. -/
theorem finite_of_boundedLiftCover {n B : ℕ} {G : Type*}
    (C : BoundedLiftCover n B G) : Finite G :=
  Finite.of_surjective C.actionOf C.covers

/-- With explicit `Fintype` data, the number of projective actions is bounded
by the number of physical labels.  This is only an upper bound because lift
presentations need not be unique. -/
theorem card_le_boundedPhaseLabel {n B : ℕ} {G : Type*} [Fintype G]
    (C : BoundedLiftCover n B G) :
    Fintype.card G ≤ Fintype.card (BoundedPhaseLabel n B) :=
  Fintype.card_le_of_surjective C.actionOf C.covers

/-- Physical-to-logical restriction cannot increase element order.

This is the abstract group-theoretic content of the paper's `m ∣ q`: when
`x` is a finite physical lift of exact order `q`, the order of its projective
logical image divides `q`. -/
theorem logicalOrder_dvd_physicalOrder {Physical Logical : Type*}
    [Group Physical] [Group Logical]
    (restriction : Physical →* Logical) (x : Physical) :
    orderOf (restriction x) ∣ orderOf x :=
  orderOf_map_dvd restriction x

/-- A surjective restriction of a commutative physical group is commutative.

For the paper, the source is the group of code-preserving diagonal product
operations (or its scalar quotient).  This lemma isolates the elementary
abelianity step from the genuinely Lie-theoretic finiteness step. -/
theorem mul_comm_of_surjective_restriction
    {Physical Logical : Type*} [CommGroup Physical] [Group Logical]
    (restriction : Physical →* Logical)
    (onto : Function.Surjective restriction) :
    ∀ g h : Logical, g * h = h * g := by
  intro g h
  obtain ⟨x, rfl⟩ := onto g
  obtain ⟨y, rfl⟩ := onto h
  calc
    restriction x * restriction y = restriction (x * y) :=
      (restriction.map_mul x y).symm
    _ = restriction (y * x) := by rw [mul_comm]
    _ = restriction y * restriction x := restriction.map_mul y x

/-- A faithful multiplicative character forces commutativity.  In the
rank-two application the character is the ratio of the two logical
eigenvalues. -/
theorem mul_comm_of_faithful_character {G : Type*} [Group G]
    (character : G →* ℂ) (faithful : Function.Injective character) :
    ∀ g h : G, g * h = h * g := by
  intro g h
  apply faithful
  simp only [map_mul]
  exact mul_comm _ _

/-- The bounded-cover version of the one-logical-qubit group conclusion:
finiteness comes from the finite lift labels, while cyclicity comes from the
supplied faithful phase-ratio character. -/
theorem isCyclic_of_boundedLiftCover {n B : ℕ} {G : Type*} [Group G]
    (C : BoundedLiftCover n B G)
    (character : G →* ℂ) (faithful : Function.Injective character) :
    IsCyclic G := by
  letI : Finite G := finite_of_boundedLiftCover C
  exact MainTheory.Cyclic.isCyclic_of_faithful character faithful

/-- Every element of the covered projective group has finite order dividing
the cardinality of the group.  This conclusion uses the global cover, not just
an element-by-element finite-lift witness. -/
theorem projectiveOrder_dvd_groupCard {G : Type*} [Group G] [Fintype G] (g : G) :
    orderOf g ∣ Fintype.card G :=
  orderOf_dvd_card

end MainTheory.ProjectiveGroupFinite
