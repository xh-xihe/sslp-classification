import MainTheory.ProjectiveGroupGeneral
import MainTheory.SortedNormalForm

/-!
# `thm:rank-two-sslp` with its canonical-angle clause

`RankTwoSSLP.rank_two_sslp` proves the theorem's cyclicity, its lift, and its
two-fibre eigenbasis, but returns the angle as a bare `a : Fin n -> ZMod q`.
The theorem's `eq:a-canonical` asks for more: the angle sorted,
`0 <= a_1 <= ... <= a_n < q`, and primitive, `gcd(q, a_1, ..., a_n) = 1`.

That normal form exists -- it is `SortedForm.SortedNormalForm`, whose `sorted`,
`lt_q` and `primitive` fields are exactly the three conditions -- and
`SortedForm.exists_sortedNormalForm` builds it at general `n` and the paper's
own `2 <= d`.  It could not be stated inside `RankTwoSSLP` because
`SortedNormalForm.lean` imports that file; hence this one.

The cyclicity conjunct is now also at `2 <= d` rather than `d = 3`, over
`ProjectiveGroupGeneral.cyclic_of_rank_two`.

Two clauses of the paper's statement are still not here, and neither is this
one: that the `m` returned is the order of a *generator* rather than of some
nontrivial element (`GroupOrder` documents that gap), and the converse
direction at general `n`.
-/

namespace MainTheory.RankTwoSSLPCanonical

open MainTheory
open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.SortedForm

variable {n : ℕ}

/-- **`thm:rank-two-sslp`, with `eq:a-canonical`.**

At the paper's own `2 <= d`: the intrinsic projective diagonal group is cyclic
and finite, and the two logical words sit in the two residue fibres of a
*sorted, in-range, primitive* angle vector, with `2 <= q`, `2 <= m` and
`m | q`.

Every clause after the group ones is a field of the returned record:
`S.sorted` and `S.lt_q` are `0 <= a_1 <= ... <= a_n < q`, `S.primitive` is
`gcd(q, a) = 1`, `S.leftFiber` and `S.rightFiber` are `eq:0L-fiber` and
`eq:1L-fiber`, `S.hasDistance` is the genuine Knill--Laflamme predicate, and
`S.source_span` with `S.frame_eq` are the paper's "up to local `X`
conjugation and permutation of the physical qubits". -/
theorem rank_two_sslp_canonical {d : ℕ} (hd : 2 ≤ d)
    (C : CodeSpec.ExactCode n 2 d) (theta : Fin n → ℝ)
    (hpres : CodeSpec.CodePreserving C.frame
      (PhaseSectorBridge.realGateEnd theta))
    (hnt : ¬ CodeSpec.SameProjectiveOnCode C.frame
      (PhaseSectorBridge.realGateEnd theta) LinearMap.id) :
    IsCyclic (IntrinsicProjectiveDiagonalLogicalGroup
      (CodeProjector.ofFrame C.frame)) ∧
    Finite (IntrinsicGroup C) ∧
    ∃ S : SortedNormalForm C,
      2 ≤ S.q ∧ 2 ≤ S.m ∧ S.m ∣ S.q ∧
      Monotone (fun j => (S.angle j).val) ∧
      (∀ j, (S.angle j).val < S.q) ∧
      Gate.Primitive S.q S.angle := by
  obtain ⟨S, _⟩ := exists_sortedNormalForm hd C theta hpres hnt
  exact ⟨MainTheory.ProjectiveGroupGeneral.cyclic_of_rank_two C hd,
    MainTheory.GeneralFinitenessRank.finite_intrinsicGroup C hd,
    S, S.two_le_q, S.two_le_m, S.m_dvd_q, S.sorted, S.lt_q, S.primitive⟩

end MainTheory.RankTwoSSLPCanonical
