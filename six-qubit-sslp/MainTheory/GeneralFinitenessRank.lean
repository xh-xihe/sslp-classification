import MainTheory.QuantitativeGroup
import MainTheory.FiniteGateAsPhase
import MainTheory.PhaseTranscription
import MainTheory.BetaExists
import MainTheory.LabelledGates

/-!
# Finiteness of the intrinsic group at arbitrary rank and `d >= 2`

`thm:finite-projective-group` is stated for any code detecting every `Z_j`.
`FiniteProjectiveGroup.whole_of_finite` assembles all four of its clauses at
arbitrary `K`, but takes `Finite (IntrinsicGroup C)` as a hypothesis, and the
only unconditional supplier was `GeneralFiniteness.finite_intrinsicGroup`,
typed at `ExactCode n 2 3`.  Every cyclicity route in the repository takes the
same hypothesis, so the whole `K > 2` branch, and the whole `d = 2` branch of
`cor:K2-q-bound` and `thm:d2-sslp-classification`, stalled on that one
instance.

They need no new mathematics, and in particular no Cartan closed-subgroup
theorem -- an earlier note in the README said otherwise and was wrong.  The
engine is already general:

* `QuantitativeGroup.quantitative_projective_group` is stated at arbitrary
  `(n, K, d)` with the paper's own `2 <= d`, and gives every nontrivial class a
  primitive lift of modulus at most any `B` with `BetaBound (n+K-1) B`;
* `BetaExists.betaBound_betaOf` supplies such a `B` unconditionally at every
  size, by pigeonhole over the finitely many zero--one matrices;
* `FiniteGateAsPhase.exists_label_of_phaseOfAngle_le` turns a modulus bound
  into a `BoundedPhaseLabel`, on a bare local phase, with no code and no `K`;
* `BoundedRepresentation.finite_of_representation` turns a per-class bounded
  label into finiteness of the quotient.

Only the last was typed at `K = 2`, decoratively: its bodies mention only
`exactCodeProjector`, `IntrinsicGroup` and `C.frame`, all rank-generic.  It is
now stated at arbitrary `K`, and this file joins the four.

What does **not** generalize is the sharp value.  The bound obtained here is
`beta_{n+K-1}`, which at `K = 2` is `beta_{n+1}` -- the cutoff of
`cor:K2-q-bound`, not the `beta_n` of `thm:d3-bound`.  The improvement to
`beta_n` is what the common affine span buys, and that argument is distance
three: it rests on equal second moments, which `SixQubit.CodeBridge` derives
from weight-two Knill--Laflamme rows.
-/

namespace MainTheory.GeneralFinitenessRank

open MainTheory
open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge
open MainTheory.ProjectiveGroupFinite
open MainTheory.BoundedRepresentation

variable {n K d : ℕ}

/-- **A primitive lift of bounded modulus names its class by a bounded
label.**

This is the one step that was missing.  `HasPrimitiveLift` already carries the
symmetry `u` in the normal form `finiteLocalPhase zeta a`, and
`PhaseTranscription.phaseOfAngle_eq_finiteLocalPhase` identifies that with the
`phaseOfAngle` the label lemma consumes. -/
theorem boundedLabel_of_hasPrimitiveLift {B q : ℕ}
    {C : CodeSpec.ExactCode n K d} {g : IntrinsicGroup C}
    (hqB : q ≤ B) (h : GeneralLiftOrder.HasPrimitiveLift C g q) :
    ∃ (lbl : BoundedPhaseLabel n B)
      (u : diagonalSymmetryGroup (exactCodeProjector C)),
      intrinsicClass (exactCodeProjector C) u = g ∧
        (u : LocalPhase n) = gateOfLabel lbl := by
  obtain ⟨hq, a, u, _, hcoe, hclass⟩ := h
  haveI := hq
  obtain ⟨lbl, hlbl⟩ :=
    MainTheory.FiniteGateAsPhase.exists_label_of_phaseOfAngle_le hqB
      (D3NormalizedFiniteToReal.canonicalRoot q)
      (D3NormalizedFiniteToReal.canonicalRoot_primitive q).pow_eq_one a
  refine ⟨lbl, u, hclass, ?_⟩
  rw [hcoe, ← MainTheory.PhaseTranscription.phaseOfAngle_eq_finiteLocalPhase]
  exact hlbl.symm

/-- **Every class of the intrinsic group has a bounded label**, at arbitrary
rank and at the paper's own `2 <= d`. -/
theorem hasBoundedRepresentation_general (C : CodeSpec.ExactCode n K d)
    (hd : 2 ≤ d) :
    HasBoundedRepresentation (MainTheory.BetaExists.betaOf (n + K - 1)) C := by
  intro g
  by_cases hg : g = 1
  · subst hg
    exact ⟨MainTheory.LabelledGates.trivialLabel
        (MainTheory.BetaExists.betaOf_pos _), 1, rfl,
      by rw [MainTheory.LabelledGates.gateOfLabel_trivial]; rfl⟩
  · obtain ⟨q, hlift, _, _, _, _, hqB⟩ :=
      MainTheory.QuantitativeGroup.quantitative_projective_group
        (MainTheory.BetaExists.betaBound_betaOf (n + K - 1)) C hd g hg
    exact boundedLabel_of_hasPrimitiveLift hqB hlift

set_option maxHeartbeats 1000000 in
/-- **The intrinsic projective diagonal group is finite**, at arbitrary rank
and at `2 <= d`.

This is the hypothesis `FiniteProjectiveGroup.whole_of_finite` was waiting
for, and the one every cyclicity route in the repository assumes. -/
theorem finite_intrinsicGroup (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d) :
    Finite (IntrinsicGroup C) :=
  finite_of_representation (hasBoundedRepresentation_general C hd)

end MainTheory.GeneralFinitenessRank
