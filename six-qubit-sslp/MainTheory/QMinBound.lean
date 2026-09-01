import MainTheory.PrimitiveReduction
import MainTheory.GeneralLiftOrder
import MainTheory.BoundedRepresentationCertified
import MainTheory.GeneralFiniteness

/-!
# `eq:6qubit-d3-bound`: `q_min <= beta_6 = 9`

Every bound in this development first produces a *representative* of a
projective class and only then asks whether it is primitive.  `q_min` is a
minimum over primitive representatives, so the two are joined by
`PrimitiveReduction`: dividing a gate's angle and modulus by their common
divisor gives the same local phase, with a primitive angle and a modulus that
divides the old one.

With that, a bounded representative bounds `q_min`, and the six-qubit
certificate `beta_6 = 9` gives the paper's boxed inequality with no hypothesis.
-/

namespace MainTheory.QMinBound

open MainTheory
open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.D3NormalizedFiniteToReal
open MainTheory.PrimitiveReduction
open MainTheory.GeneralLiftOrder

noncomputable section

variable {n K d : ℕ}

/-- A labelled gate is the finite local phase of its own label. -/
theorem gateOfLabel_eq_finiteLocalPhase {B : ℕ}
    (lbl : ProjectiveGroupFinite.BoundedPhaseLabel n B) :
    letI : NeZero (lbl.1.val + 1) := ⟨Nat.succ_ne_zero _⟩
    BoundedRepresentation.gateOfLabel lbl
      = finiteLocalPhase (canonicalRoot (lbl.1.val + 1))
          (canonicalRoot_primitive (lbl.1.val + 1)) lbl.2 := by
  letI : NeZero (lbl.1.val + 1) := ⟨Nat.succ_ne_zero _⟩
  funext j
  refine Subtype.ext ?_
  simp only [finiteLocalPhase, coe_residueUnitary, Cyclic.chi]
  have hq : 0 < lbl.1.val + 1 := Nat.succ_pos _
  have hcast : ((lbl.1.val : ℝ)) + 1 = ((lbl.1.val + 1 : ℕ) : ℝ) := by
    push_cast; ring
  show ((BoundedRepresentation.gateOfLabel lbl j : unitary ℂ) : ℂ) = _
  rw [BoundedRepresentation.gateOfLabel, hcast,
    LabelledGates.circlePhase_eq_canonicalRoot_pow _ _ hq]
  congr 1

/-- **A bounded class has a primitive lift of no larger modulus.** -/
theorem exists_primitiveLift_le_of_boundedClass {B : ℕ}
    {C : CodeSpec.ExactCode n K d} {g : IntrinsicGroup C}
    (h : BoundedClassPower.BoundedClass B (exactCodeProjector C) g) :
    ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ HasPrimitiveLift C g q := by
  obtain ⟨lbl, u, hclass, hgate⟩ := h
  set q0 := lbl.1.val + 1 with hq0
  have hq0pos : 0 < q0 := Nat.succ_pos _
  letI : NeZero q0 := ⟨hq0pos.ne'⟩
  have hq0B : q0 ≤ B := lbl.1.isLt
  set q1 := reducedModulus q0 lbl.2 with hq1
  have hq1pos : 0 < q1 := reducedModulus_pos hq0pos lbl.2
  letI : NeZero q1 := ⟨hq1pos.ne'⟩
  refine ⟨q1, hq1pos, le_trans (reducedModulus_le q0 lbl.2) hq0B,
    inferInstance, reducedAngle q0 lbl.2, u,
    primitive_reducedAngle hq0pos lbl.2, ?_, hclass⟩
  rw [hgate, gateOfLabel_eq_finiteLocalPhase lbl]
  exact finiteLocalPhase_reduced hq0pos lbl.2

/-- **`q_min` is bounded by any bounded representation.** -/
theorem qMin_le_of_boundedClass {B : ℕ} (C : CodeSpec.ExactCode n K d)
    (hd : 2 ≤ d) (g : IntrinsicGroup C)
    (h : BoundedClassPower.BoundedClass B (exactCodeProjector C) g) :
    qMin C hd g ≤ B := by
  obtain ⟨q, hqpos, hqB, hlift⟩ := exists_primitiveLift_le_of_boundedClass h
  exact le_trans (qMin_le C hd g hqpos hlift) hqB

/-- **`eq:6qubit-d3-bound`.**

`q_min(U) <= beta_6 = 9` for every projective diagonal logical element of an
exact `((6,2,3))` code, with no hypothesis: `beta_6 = 9` is a kernel theorem and
the bounded representation it feeds is unconditional. -/
theorem qMin_le_nine (C : CodeSpec.ExactCode 6 2 3)
    (g : IntrinsicGroup C) :
    qMin C GeneralFiniteness.two_le_three g ≤ 9 :=
  qMin_le_of_boundedClass C GeneralFiniteness.two_le_three g
    (BoundedRepresentationCertified.hasBoundedRepresentation_unconditional C g)

/-! ## `thm:d3-bound`, with the same projective element -/

/-- **`thm:d3-bound`.**

The *same* projective logical element -- not a coprime power of it -- has a
primitive finite physical lift `D(a;q)` with `q <= beta_n` and `m | q`.

`D3BoundedNormalForm.d3_bound` produces a generator of the same cyclic group;
this produces a lift of the element itself, because the bounded-representation
route keeps the class fixed and `PrimitiveReduction` makes its representative
primitive without enlarging the modulus. -/
theorem d3_bound_same_class {B : ℕ} (beta : BinaryBeta.BetaBound n B)
    (hB : 0 < B) (C : CodeSpec.ExactCode n 2 3) (g : IntrinsicGroup C) :
    ∃ q : ℕ, 0 < q ∧ q ≤ B ∧ HasPrimitiveLift C g q ∧ orderOf g ∣ q := by
  obtain ⟨q, hqpos, hqB, hlift⟩ :=
    exists_primitiveLift_le_of_boundedClass
      (GeneralFiniteness.hasBoundedRepresentation_general beta hB C g)
  exact ⟨q, hqpos, hqB, hlift, orderOf_dvd_of_hasPrimitiveLift hlift⟩

/-- **The six-qubit instance**, unconditional: every projective diagonal
logical element of an exact `((6,2,3))` code has a primitive lift of modulus at
most nine, and its order divides that modulus. -/
theorem d3_bound_nine (C : CodeSpec.ExactCode 6 2 3) (g : IntrinsicGroup C) :
    ∃ q : ℕ, 0 < q ∧ q ≤ 9 ∧ HasPrimitiveLift C g q ∧ orderOf g ∣ q := by
  obtain ⟨q, hqpos, hqB, hlift⟩ :=
    exists_primitiveLift_le_of_boundedClass
      (BoundedRepresentationCertified.hasBoundedRepresentation_unconditional C g)
  exact ⟨q, hqpos, hqB, hlift, orderOf_dvd_of_hasPrimitiveLift hlift⟩

end

end MainTheory.QMinBound
