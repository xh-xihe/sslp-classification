import MainTheory.GeneralFinitenessRank
import MainTheory.FiniteProjectiveGroup
import MainTheory.RankTwoSSLP

/-!
# `thm:finite-projective-group` and the cyclicity of `cor:K2-q-bound`, without
# a rank or distance restriction

`FiniteProjectiveGroup.whole_of_finite` and `RankTwoSSLP.cyclic_of_finite` are
sockets: each assembles its paper statement from `Finite (IntrinsicGroup C)`,
which until now had no unconditional supplier outside `ExactCode n 2 3`.
`GeneralFinitenessRank.finite_intrinsicGroup` is the plug, so this file is
three applications.

The distance hypothesis is the paper's own `d >= 2` throughout, and the rank
is arbitrary where the paper's is.  What is *not* claimed here is any sharp
modulus: the bound behind the finiteness is `beta_{n+K-1}`, which at `K = 2`
is `cor:K2-q-bound`'s `beta_{n+1}` and not `thm:d3-bound`'s `beta_n`.
-/

namespace MainTheory.ProjectiveGroupGeneral

open MainTheory
open MainTheory.ClassificationLevels
open MainTheory.GlobalClassificationBridge

variable {n K d : ℕ}

/-- **`thm:finite-projective-group`, unconditionally.**

At arbitrary rank and at the paper's own `2 <= d`: the intrinsic projective
diagonal group is finite and abelian, every class has a primitive finite lift,
and every class's order divides every such lift's modulus.

`FiniteProjectiveGroup.whole` had the same conclusion but only at `K = 2`,
`d = 3`. -/
theorem whole (C : CodeSpec.ExactCode n K d) (hd : 2 ≤ d) :
    Finite (IntrinsicGroup C) ∧
    (∀ g h : IntrinsicGroup C, g * h = h * g) ∧
    (∀ g : IntrinsicGroup C, ∃ q : ℕ, 0 < q ∧
      GeneralLiftOrder.HasPrimitiveLift C g q) ∧
    (∀ (g : IntrinsicGroup C) (q : ℕ),
      GeneralLiftOrder.HasPrimitiveLift C g q → orderOf g ∣ q) :=
  MainTheory.FiniteProjectiveGroup.whole_of_finite C hd
    (MainTheory.GeneralFinitenessRank.finite_intrinsicGroup C hd)

/-- **The cyclicity sentence of `cor:K2-q-bound`, at its own hypothesis.**

`RankTwoSSLP.cyclic_of_finite` proved this from finiteness; the paper asserts
it at `d >= 2`, and that is now where it holds. -/
theorem cyclic_of_rank_two (C : CodeSpec.ExactCode n 2 d) (hd : 2 ≤ d) :
    IsCyclic (IntrinsicProjectiveDiagonalLogicalGroup
      (CodeProjector.ofFrame C.frame)) :=
  MainTheory.RankTwoSSLP.cyclic_of_finite C
    (MainTheory.GeneralFinitenessRank.finite_intrinsicGroup C hd)

/-- **`cor:K2-q-bound` with both of its sentences**, at `d >= 2`: the modulus
bound and the cyclicity, for a code of rank two. -/
theorem k2_bound_and_cyclic {B : ℕ}
    (beta : MainTheory.BinaryBeta.BetaBound (n + 1) B)
    (C : CodeSpec.ExactCode n 2 d) (hd : 2 ≤ d) :
    IsCyclic (IntrinsicProjectiveDiagonalLogicalGroup
      (CodeProjector.ofFrame C.frame)) ∧
    Finite (IntrinsicGroup C) ∧
    ∀ g : IntrinsicGroup C, g ≠ 1 → ∃ q : ℕ,
      GeneralLiftOrder.HasPrimitiveLift C g q ∧
      orderOf g ∣ q ∧ orderOf g ≤ q ∧ 2 ≤ q ∧ q ≤ B := by
  refine ⟨cyclic_of_rank_two C hd,
    MainTheory.GeneralFinitenessRank.finite_intrinsicGroup C hd, ?_⟩
  intro g hg
  obtain ⟨q, hlift, hdvd, _, hle, hq2, hqB⟩ :=
    MainTheory.QuantitativeGroup.quantitative_projective_group
      (by simpa using beta) C hd g hg
  exact ⟨q, hlift, hdvd, hle, hq2, hqB⟩

end MainTheory.ProjectiveGroupGeneral
