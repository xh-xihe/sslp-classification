import MainTheory.GeneralFiniteness

/-!
# `thm:rank-two-sslp` as one statement

The forward direction of the paper's rank-two theorem is proved in this
repository, but it lives as a chain of separately stated results plus a
thirty-field certificate record.  An independent audit observed that anyone
reading only a top-level name would not find the theorem, and that the audit
itself had to reassemble it.

This file states it once, at general `n`, in the paper's own shape:

> for an exact `((n,2,d))` code with `d >= 2` whose projective diagonal group
> is nontrivial, that group is cyclic; a nontrivial element has a primitive
> root-of-unity physical lift `D(a;q)` with `q >= 2`; its projective logical
> order `m` satisfies `2 <= m` and `m | q`; and after conjugating by a local
> `X` string and multiplying the angle by a unit, the two logical states are
> supported in the residue fibres `0` and `q/m`.

The paper's proof splits at exactly one place, and so does this file.  The
two-fibre half needs only a projectively nontrivial diagonal operation, and is
proved at the paper's own hypothesis `d >= 2` (`two_fibre_normal_form`).
Cyclicity needs the group to be finite, which the paper takes from its
`thm:finite-projective-group`; `cyclic_of_finite` takes that as a hypothesis
at general `d`, and `rank_two_sslp` discharges it at `d = 3`, where the
distance-three rationalization proves finiteness outright.  At `d = 2`
finiteness is still only available by the paper's compact-Lie-group route,
which Mathlib cannot support.

Two things are deliberately not bundled in.  The sorted canonical form
`a_1 <= ... <= a_n < q` with `gcd(q, a_1, ..., a_n) = 1` is a separate record,
`SortedForm.SortedNormalForm`, built by `SortedForm.exists_sortedNormalForm`;
keeping it apart is what lets this statement name the eigenframe without a
permutation in the way.  The converse is `RankTwo.order_of_two_fiber`, which
is complete and general: a pair supported in the residue-`0` and residue-`q/m`
fibres is acted on diagonally with projective order exactly `m`.
-/

namespace MainTheory.RankTwoSSLP

open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.SectionTwoGeneral
open MainTheory.D3NormalizedFreshPhase

variable {n : ℕ}

/-- **The two-fibre normal form, at the paper's own hypothesis `d >= 2`.**

No finiteness is used or assumed: a projectively nontrivial diagonal operation
alone yields the primitive lift and the two fibres.  The `HasDistance` clause
records that the normalized pair is still an exact distance-`d` code, which is
what the paper's converse takes as its hypothesis.

The clause `∃ g, orderOf g = m` is what stops `m` from being a free number
satisfying two inequalities: it is the order of an actual element of the
intrinsic group, which is the paper's `C_m`. -/
theorem two_fibre_normal_form {d : ℕ} (hd : 2 ≤ d)
    (C : CodeSpec.ExactCode n 2 d) (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    ∃ (q : ℕ) (_ : NeZero q) (zeta : ℂ) (a : Fin n → ZMod q)
      (F : CodeSpec.OrthonormalFrame n 2)
      (m : ℕ) (x0 : SS.BitString n) (u : (ZMod q)ˣ),
      CodeSpec.codeSpan C.frame = CodeSpec.codeSpan F ∧
      IsPrimitiveRoot zeta q ∧
      Gate.Primitive q a ∧
      2 ≤ q ∧ 2 ≤ m ∧ m ∣ q ∧
      (∃ g : IntrinsicGroup C, orderOf g = m) ∧
      SS.HasDistance (fun k s => F.vec k (SS.bxor s x0)) d ∧
      CodeSpec.SameProjectiveOnCode C.frame
        (RankTwoGlobal.finiteGateEnd zeta a)
        (PhaseSectorBridge.realGateEnd theta) ∧
      SS.SSConditionState
        (fun j => (u : ZMod q) * Normalize.flip a x0 j) 0
        (fun s => F.vec 0 (SS.bxor s x0)) ∧
      SS.SSConditionState
        (fun j => (u : ZMod q) * Normalize.flip a x0 j)
        (((q / m : ℕ) : ZMod q))
        (fun s => F.vec 1 (SS.bxor s x0)) := by
  letI : NeZero (rationalLift C hd theta hpres).order :=
    ⟨(rationalLift C hd theta hpres).order_pos.ne'⟩
  set G := finiteGenerator C hd theta hpres hnt with hG
  set T := canonicalTwoFiber G with hT
  refine ⟨(rationalLift C hd theta hpres).order, inferInstance,
    G.zeta, G.angle, G.eigenFrame, T.logicalOrder, T.x0, T.unit,
    G.span_eq, G.primitiveRoot, G.primitive,
    T.two_le_physicalOrder, T.two_le_logicalOrder,
    T.logicalOrder_dvd_physical, ⟨G.intrinsicClass, T.intrinsic_order_eq⟩,
    T.normalizedHasDistance, ?_, T.normalizedLeft, T.normalizedRight⟩
  exact finiteGenerator_sameProjective C hd theta hpres hnt

/-- **The same, under the paper's own hypothesis.**

`thm:rank-two-sslp` assumes the projective diagonal group is nontrivial, which
is a statement about the group; `two_fibre_normal_form` instead takes a real
phase vector already known to act projectively nontrivially.  The two are
equivalent, and the translation is done here rather than left to the reader:
a class other than the identity has a representative, every local phase is an
exponential, and a nontrivial class makes that exponential projectively
nontrivial. -/
theorem two_fibre_normal_form_of_nontrivial {d : ℕ} (hd : 2 ≤ d)
    (C : CodeSpec.ExactCode n 2 d)
    (hnontrivial : ∃ g : IntrinsicGroup C, g ≠ 1) :
    ∃ (q : ℕ) (_ : NeZero q) (zeta : ℂ) (a : Fin n → ZMod q)
      (F : CodeSpec.OrthonormalFrame n 2)
      (m : ℕ) (x0 : SS.BitString n) (u : (ZMod q)ˣ)
      (theta : Fin n → ℝ),
      CodeSpec.codeSpan C.frame = CodeSpec.codeSpan F ∧
      IsPrimitiveRoot zeta q ∧
      Gate.Primitive q a ∧
      2 ≤ q ∧ 2 ≤ m ∧ m ∣ q ∧
      (∃ g : IntrinsicGroup C, orderOf g = m) ∧
      SS.HasDistance (fun k s => F.vec k (SS.bxor s x0)) d ∧
      CodeSpec.SameProjectiveOnCode C.frame
        (RankTwoGlobal.finiteGateEnd zeta a)
        (PhaseSectorBridge.realGateEnd theta) ∧
      SS.SSConditionState
        (fun j => (u : ZMod q) * Normalize.flip a x0 j) 0
        (fun s => F.vec 0 (SS.bxor s x0)) ∧
      SS.SSConditionState
        (fun j => (u : ZMod q) * Normalize.flip a x0 j)
        (((q / m : ℕ) : ZMod q))
        (fun s => F.vec 1 (SS.bxor s x0)) := by
  obtain ⟨g, hg1⟩ := hnontrivial
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨theta, hexp⟩ :=
    MainTheory.LocalPhaseAngle.exists_angleVector (v : LocalPhase n)
  have hpres := SymmetryToEntrance.codePreserving_of_symmetry C.frame
    (v : LocalPhase n) v.2 theta hexp
  have hnt := SymmetryToEntrance.projectivelyNontrivialReal_of_class_ne_one
    C (v : LocalPhase n) v.2 theta hexp hg1
  obtain ⟨q, hq, zeta, a, F, m, x0, u, h⟩ :=
    two_fibre_normal_form hd C theta hpres hnt
  exact ⟨q, hq, zeta, a, F, m, x0, u, theta, h⟩

/-- **Cyclicity, at general `d`, from finiteness.**

This is the one place the paper's proof of `thm:rank-two-sslp` reaches outside
itself, to `thm:finite-projective-group`; the hypothesis is stated rather than
hidden.  No nontriviality is needed: if every symmetry is projectively trivial
the group is a subsingleton, which is cyclic, and the paper's nontriviality
assumption is only what makes `m >= 2`. -/
theorem cyclic_of_finite {d : ℕ} (C : CodeSpec.ExactCode n 2 d)
    (hfin : Finite (IntrinsicGroup C)) :
    IsCyclic (IntrinsicProjectiveDiagonalLogicalGroup
      (CodeProjector.ofFrame C.frame)) := by
  by_cases h : ∃ u0 : diagonalSymmetryGroup (CodeProjector.ofFrame C.frame),
      ¬ IsProjectivelyTrivial (CodeProjector.ofFrame C.frame) u0
  · obtain ⟨u0, h0⟩ := h
    exact LogicalCharacter.isCyclic_of_nontrivial C u0 h0 hfin
  · push_neg at h
    haveI : Subsingleton (IntrinsicProjectiveDiagonalLogicalGroup
        (CodeProjector.ofFrame C.frame)) := by
      constructor
      intro a b
      refine QuotientGroup.induction_on a (fun x => ?_)
      refine QuotientGroup.induction_on b (fun y => ?_)
      rw [QuotientGroup.eq]
      exact h _
    infer_instance

/-- **The rank-two SSLP normal form, in one statement.**

The two-fibre clauses are about an orthonormal eigenframe `F` spanning the
same code, not about `C.frame` itself; that is the paper's "up to local `X`
conjugation and logical-state interchange", and `span_eq` is what ties `F`
back to `C`.

Stated at `d = 3`, which is where finiteness is unconditional here.  The
two-fibre content holds at `d >= 2` -- see `two_fibre_normal_form`. -/
theorem rank_two_sslp (C : CodeSpec.ExactCode n 2 3)
    (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    IsCyclic (IntrinsicProjectiveDiagonalLogicalGroup
        (CodeProjector.ofFrame C.frame)) ∧
    Finite (IntrinsicGroup C) ∧
    ∃ (q : ℕ) (_ : NeZero q) (zeta : ℂ) (a : Fin n → ZMod q)
      (F : CodeSpec.OrthonormalFrame n 2)
      (m : ℕ) (x0 : SS.BitString n) (u : (ZMod q)ˣ),
      CodeSpec.codeSpan C.frame = CodeSpec.codeSpan F ∧
      IsPrimitiveRoot zeta q ∧
      Gate.Primitive q a ∧
      2 ≤ q ∧ 2 ≤ m ∧ m ∣ q ∧
      (∃ g : IntrinsicGroup C, orderOf g = m) ∧
      SS.HasDistance (fun k s => F.vec k (SS.bxor s x0)) 3 ∧
      CodeSpec.SameProjectiveOnCode C.frame
        (RankTwoGlobal.finiteGateEnd zeta a)
        (PhaseSectorBridge.realGateEnd theta) ∧
      SS.SSConditionState
        (fun j => (u : ZMod q) * Normalize.flip a x0 j) 0
        (fun s => F.vec 0 (SS.bxor s x0)) ∧
      SS.SSConditionState
        (fun j => (u : ZMod q) * Normalize.flip a x0 j)
        (((q / m : ℕ) : ZMod q))
        (fun s => F.vec 1 (SS.bxor s x0)) :=
  ⟨GeneralFiniteness.isCyclic C, GeneralFiniteness.finite_intrinsicGroup C,
    two_fibre_normal_form GeneralFiniteness.two_le_three C theta hpres hnt⟩

end MainTheory.RankTwoSSLP
