import MainTheory.GeneralFiniteness

/-!
# `thm:rank-two-sslp` as one statement

The forward direction of the paper's rank-two theorem is proved in this
repository, but it lives as a chain of separately stated results plus a
thirty-field certificate record.  An independent audit observed that anyone
reading only a top-level name would not find the theorem, and that the audit
itself had to reassemble it.

This file states it once, at general `n`, in the paper's own shape:

> for an exact `((n,2,3))` code whose projective diagonal group is nontrivial,
> that group is finite cyclic; a nontrivial element has a primitive
> root-of-unity physical lift `D(a;q)` with `q >= 2`; its projective logical
> order `m` satisfies `2 <= m` and `m | q`; and after conjugating by a local
> `X` string and multiplying the angle by a unit, the two logical states are
> supported in the residue fibres `0` and `q/m`.

Two things are deliberately not bundled in.  The sorted canonical form
`a_1 <= ... <= a_n < q` is a separate record, `SortedForm.SortedNormalForm`,
built by `SortedForm.exists_sortedNormalForm`; keeping it apart is what lets
this statement name the eigenframe without a permutation in the way.  The
converse is `RankTwo.order_of_two_fiber`, which is complete and general: a
pair supported in the residue-`0` and residue-`q/m` fibres is acted on
diagonally with projective order exactly `m`.
-/

namespace MainTheory.RankTwoSSLP

open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.SectionTwoGeneral
open MainTheory.D3NormalizedFreshPhase

variable {n : ℕ}

/-- **The rank-two SSLP normal form, in one statement.**

The two-fibre clauses are about an orthonormal eigenframe `F` spanning the
same code, not about `C.frame` itself; that is the paper's "up to local `X`
conjugation and logical-state interchange", and `span_eq` is what ties `F`
back to `C`.

The clause `∃ g, orderOf g = m` is what stops `m` from being a free number
satisfying two inequalities: it is the order of an actual element of the
intrinsic group, which is the paper's `C_m`.  `MainTheory/GroupOrder.lean`
carries that further, to `m | Nat.card` and to when the two are equal. -/
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
  refine ⟨GeneralFiniteness.isCyclic C,
    GeneralFiniteness.finite_intrinsicGroup C, ?_⟩
  letI : NeZero (rationalLift C GeneralFiniteness.two_le_three theta hpres).order :=
    ⟨(rationalLift C GeneralFiniteness.two_le_three theta hpres).order_pos.ne'⟩
  set G := finiteGenerator C GeneralFiniteness.two_le_three theta hpres hnt with hG
  set T := canonicalTwoFiber G with hT
  refine ⟨(rationalLift C GeneralFiniteness.two_le_three theta hpres).order, inferInstance,
    G.zeta, G.angle, G.eigenFrame, T.logicalOrder, T.x0, T.unit,
    G.span_eq, G.primitiveRoot, G.primitive,
    T.two_le_physicalOrder, T.two_le_logicalOrder,
    T.logicalOrder_dvd_physical, ⟨G.intrinsicClass, T.intrinsic_order_eq⟩,
    ?_, T.normalizedLeft, T.normalizedRight⟩
  exact finiteGenerator_sameProjective C GeneralFiniteness.two_le_three theta hpres hnt

end MainTheory.RankTwoSSLP
