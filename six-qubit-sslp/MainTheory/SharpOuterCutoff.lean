import MainTheory.SSLPCompleteness
import MainTheory.BetaExists

/-!
# `eq:Bnd0` at the manuscript's own constants

`SSLPCompleteness.outerCutoff B1 Bn d0 = if d0 <= 2 then B1 else Bn` renders
the case split of `eq:Bnd0`, but with the two branch values left free: the
completeness theorems only require `BinaryBeta.BetaBound (n+1) B1` and
`BetaBound n Bn`, which are *upper* bounds, so the Lean cutoff may be strictly
larger than the manuscript's `beta_{n+1}` and `beta_n`.  That is harmless for
a covering statement and it is not the display.

The sharp quantity is already in the repository: `BetaExists.betaOf N` is
literally the supremum over sizes at most `N` of the largest zero-one inverse
denominator, and `betaBound_betaOf` says it is a `BetaBound`.  Instantiating
both branches there makes `outerCutoff` the manuscript's `B_{n,d_0}`, and
gives the completeness statements with the manuscript's own bound in place of
a free parameter.
-/

namespace MainTheory.SharpOuterCutoff

open MainTheory
open MainTheory.SSLPCompleteness

variable {n : ℕ}

/-- **`eq:Bnd0` verbatim.**  The controlled outer cutoff at the sharp
constants: `beta_{n+1}` at target distance two, `beta_n` at target distance
three or more, both of them genuine `BetaBound`s. -/
theorem outerCutoff_betaOf (n : ℕ) :
    BinaryBeta.BetaBound (n + 1) (BetaExists.betaOf (n + 1)) ∧
      BinaryBeta.BetaBound n (BetaExists.betaOf n) ∧
      outerCutoff (BetaExists.betaOf (n + 1)) (BetaExists.betaOf n) 2
        = BetaExists.betaOf (n + 1) ∧
      ∀ d0 : ℕ, 3 ≤ d0 →
        outerCutoff (BetaExists.betaOf (n + 1)) (BetaExists.betaOf n) d0
          = BetaExists.betaOf n :=
  ⟨BetaExists.betaBound_betaOf _, BetaExists.betaBound_betaOf _,
    outerCutoff_two _ _, fun _ h => outerCutoff_of_three_le _ _ h⟩

/-- **Completeness at the sharp cutoff, target distance three or more.**

`completeness_of_nontrivial_three` with both branch values instantiated at
`betaOf`, so the bound reads `S.q <= beta_n` -- the manuscript's own
`B_{n,d_0}` for `d_0 >= 3` -- instead of a free parameter. -/
theorem completeness_three_sharp {d0 d : ℕ} (hd0 : 3 ≤ d0) (hdd : d0 ≤ d)
    (C : CodeSpec.ExactCode n 2 d)
    (hnontrivial : ∃ g : GlobalClassificationBridge.IntrinsicGroup C, g ≠ 1) :
    ∃ S : SortedForm.SortedNormalForm
        (weakenDistance (show 3 ≤ d by omega) C),
      2 ≤ S.q ∧ S.q ≤ BetaExists.betaOf n ∧ 2 ≤ S.m ∧ S.m ∣ S.q ∧
      (∃ g : GlobalClassificationBridge.IntrinsicGroup
        (weakenDistance (show 3 ≤ d by omega) C), orderOf g = S.m) ∧
      Monotone (fun j => (S.angle j).val) ∧
      (∀ j, (S.angle j).val < S.q) ∧
      Gate.Primitive S.q S.angle ∧
      SS.HasDistance S.frame.vec d := by
  obtain ⟨S, h2, hq, rest⟩ := completeness_of_nontrivial_three
    (B1 := BetaExists.betaOf (n + 1)) hd0 hdd (BetaExists.betaBound_betaOf n)
    C hnontrivial
  refine ⟨S, h2, ?_, rest⟩
  rwa [outerCutoff_of_three_le _ _ hd0] at hq

end MainTheory.SharpOuterCutoff
